'use strict';
const path = require('path');
const os = require('os');
const http = require('http');
const crypto = require('crypto');
const express = require('express');
const { Server } = require('socket.io');
const QRCode = require('qrcode');
const BANK = require('./bank');

const PORT = +process.env.PORT || 3000;
const HOST_KEY = process.env.HOST_KEY || crypto.randomBytes(3).toString('hex');

const TEAMS = [
  { id: 0, name: 'الأحمر', en: 'RED', color: '#ef4444', emoji: '🟥' },
  { id: 1, name: 'الأزرق', en: 'BLUE', color: '#3b82f6', emoji: '🟦' },
  { id: 2, name: 'الأخضر', en: 'GREEN', color: '#22c55e', emoji: '🟩' },
  { id: 3, name: 'الأصفر', en: 'YELLOW', color: '#eab308', emoji: '🟨' },
];

// ───────────── helpers ─────────────
const now = () => Date.now();
const rnd = (a, b) => a + Math.random() * (b - a);
const pick = (a) => a[Math.floor(Math.random() * a.length)];
const shuffle = (a) => {
  a = [...a];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
};
const num = (v, d, lo, hi) => {
  v = Number(v);
  if (!Number.isFinite(v)) v = d;
  return Math.min(hi, Math.max(lo, v));
};
const str = (v, max = 200) => String(v ?? '').trim().slice(0, max);
const rankPts = (r) => (r === 1 ? 10 : r === 2 ? 7 : r === 3 ? 5 : r <= 10 ? 2 : 0);
const fmtT = (ms) => (ms / 1000).toFixed(2) + 'ث';

function toLatinDigits(s) {
  return s
    .replace(/[٠-٩]/g, (d) => '٠١٢٣٤٥٦٧٨٩'.indexOf(d))
    .replace(/[۰-۹]/g, (d) => '۰۱۲۳۴۵۶۷۸۹'.indexOf(d));
}
function norm(s, strict) {
  s = String(s ?? '')
    .normalize('NFC')
    .replace(/[‎‏‪-‮؜]/g, '')
    .replace(/\s+/g, ' ')
    .trim();
  if (strict) return s;
  return toLatinDigits(s)
    .toLowerCase()
    .replace(/[ً-ٰٟـ]/g, '')
    .replace(/[أإآٱ]/g, 'ا')
    .replace(/ى/g, 'ي')
    .replace(/ة/g, 'ه')
    .replace(/[^\p{L}\p{N}\s]/gu, '')
    .replace(/\s+/g, ' ')
    .trim();
}
function parseNum(v) {
  const s = toLatinDigits(String(v ?? '')).replace(/٫/g, '.').replace(/[,،٬\s]/g, '');
  if (!s) return NaN;
  return Number(s);
}
const fmtN = (n) => Number(n).toLocaleString('en', { maximumFractionDigits: 2 });

function localIps() {
  const out = [];
  const virt = /vmware|virtual|vethernet|wsl|docker|hyper-v|loopback|vpn/i;
  for (const [name, list] of Object.entries(os.networkInterfaces())) {
    for (const i of list || []) {
      if (i.family === 'IPv4' && !i.internal) out.push({ name, address: i.address });
    }
  }
  const score = (a) =>
    /^192\.168\./.test(a) ? 0 : /^10\./.test(a) ? 1 : /^172\.(1[6-9]|2\d|3[01])\./.test(a) ? 2 : 3;
  out.sort((a, b) => virt.test(a.name) - virt.test(b.name) || score(a.address) - score(b.address));
  return out;
}
const IPS = localIps();
const isLocal = (addr) => {
  addr = String(addr || '').replace('::ffff:', '');
  return addr === '::1' || addr === '127.0.0.1' || IPS.some((i) => i.address === addr);
};

// ───────────── state ─────────────
let G;
let roundSeq = 0;
function fresh() {
  G = {
    event: 'PLAYROOM',
    teamCount: 2,
    teamScores: [0, 0, 0, 0],
    players: new Map(), // token -> player
    phase: 'lobby', // lobby | round | results | final
    round: null,
    last: null,
    history: [],
    final: null,
    ip: IPS[0]?.address || 'localhost',
  };
}
fresh();

const allPlayers = () => [...G.players.values()];
const onlinePlayers = () => allPlayers().filter((p) => p.online);
const byId = (id) => allPlayers().find((p) => p.id === id);
const joinUrl = () => `http://${G.ip}:${PORT}`;

function smallestTeam() {
  const counts = Array.from({ length: G.teamCount }, () => 0);
  for (const p of allPlayers()) if (p.team < G.teamCount) counts[p.team]++;
  const min = Math.min(...counts);
  return pick(counts.map((c, i) => (c === min ? i : -1)).filter((i) => i >= 0));
}
function award(p, pts) {
  if (!pts) return;
  p.score += pts;
  G.teamScores[p.team] += pts;
}
const row = (p, pts, detail) => ({ id: p.id, name: p.name, team: p.team, pts, detail });
const randomIn = (teamId) => {
  const c = onlinePlayers().filter((p) => p.team === teamId);
  return c.length ? pick(c) : null;
};

// ───────────── games ─────────────
function later(r, ms, fn) {
  const h = setTimeout(() => {
    if (G.round === r) fn();
  }, ms);
  r.timers.push(h);
  return h;
}

const KINDS = {
  // ----- race: first correct answers win (typing / scramble / fill / memory) -----
  race: {
    start(r) {
      r.phase = 'countdown';
      r.nextAt = now() + 3000;
      const live = () => {
        r.phase = 'live';
        r.liveAt = now();
        r.endsAt = r.liveAt + r.duration * 1000;
        r.nextAt = null;
        later(r, r.duration * 1000, () => endRound('time'));
        touch(true);
      };
      later(r, 3000, () => {
        if (r.flash) {
          r.phase = 'flash';
          r.nextAt = now() + r.flash.ms;
          later(r, r.flash.ms, live);
          touch(true);
        } else live();
      });
    },
    submit(r, p, v) {
      if (r.phase !== 'live') return 'locked';
      const s = r.sub.get(p.id) || {};
      if (s.correct) return 'correct';
      if (s.dead) return 'dead';
      if (now() - (s.last || 0) < 120) return 'wait';
      s.last = now();
      r.sub.set(p.id, s);
      if (r.answers.includes(norm(v, r.strict))) {
        s.correct = true;
        s.t = now() - r.liveAt;
        r.order.push(p.id);
        if (r.order.length >= Math.min(10, onlinePlayers().length)) endRound('done');
        return 'correct';
      }
      if (r.options) s.dead = true;
      return s.dead ? 'dead' : 'wrong';
    },
    pub(r) {
      const live = r.phase === 'live';
      return {
        prompt: r.phase === 'countdown' ? null : r.prompt,
        display: live ? r.display : null,
        tiles: live ? r.tiles : null,
        options: live ? r.options : null,
        flash: r.phase === 'flash' ? r.flash.items : null,
        flashMs: r.flash ? r.flash.ms : null,
        answered: r.order.length,
      };
    },
    me(r, p) {
      const s = r.sub.get(p.id) || {};
      return { status: s.correct ? 'correct' : s.dead ? 'dead' : 'idle' };
    },
    host(r) {
      return {
        secret: r.secretText,
        live: r.order.map((id, i) => ({ name: byId(id)?.name, team: byId(id)?.team, detail: `#${i + 1} · ${fmtT(r.sub.get(id).t)}` })),
      };
    },
    finish(r) {
      const rows = r.order.map((id, i) => {
        const p = byId(id);
        const pts = rankPts(i + 1);
        if (p) award(p, pts);
        return p ? row(p, pts, fmtT(r.sub.get(id).t)) : null;
      }).filter(Boolean);
      return { answer: r.secretText, rows };
    },
  },

  // ----- closest: everyone enters a number, nearest wins -----
  closest: {
    start(r) {
      r.phase = 'live';
      r.endsAt = now() + r.duration * 1000;
      later(r, r.duration * 1000, () => endRound('time'));
    },
    submit(r, p, v) {
      if (r.phase !== 'live') return 'locked';
      const n = parseNum(v);
      if (!Number.isFinite(n)) return 'bad';
      const s = r.sub.get(p.id);
      r.sub.set(p.id, { v: n, t: s ? s.t : now() - r.startedAt });
      if (r.sub.size >= onlinePlayers().length) endRound('done');
      return 'ok:' + fmtN(n);
    },
    pub: (r) => ({ prompt: r.prompt, answered: r.sub.size }),
    me(r, p) {
      const s = r.sub.get(p.id);
      return { status: s ? 'submitted' : 'idle', value: s ? fmtN(s.v) : null };
    },
    host: (r) => ({
      secret: r.secretText,
      live: [...r.sub].map(([id, s]) => ({ name: byId(id)?.name, team: byId(id)?.team, detail: fmtN(s.v) })),
    }),
    finish(r) {
      const list = [...r.sub].map(([id, s]) => ({ id, ...s, diff: Math.abs(s.v - r.target) }));
      list.sort((a, b) => a.diff - b.diff || a.t - b.t);
      const rows = list.map((e, i) => {
        const p = byId(e.id);
        if (!p) return null;
        const pts = rankPts(i + 1);
        award(p, pts);
        return row(p, pts, `${fmtN(e.v)}${r.unit}${e.diff ? ` (فرق ${fmtN(e.diff)})` : ' ✔ تماماً'}`);
      }).filter(Boolean);
      return { answer: r.secretText, rows };
    },
  },

  // ----- buzzer: first to buzz, host judges -----
  buzzer: {
    start(r) {
      r.phase = 'live';
      r.state = 'open';
      r.holder = null;
      r.out = new Set();
      r.log = [];
      r.openAt = now();
      r.endsAt = now() + r.duration * 1000;
      later(r, r.duration * 1000, () => endRound('time'));
    },
    buzz(r, p) {
      if (r.state !== 'open' || r.out.has(p.id)) return;
      r.state = 'held';
      r.holder = p.id;
      r.buzzMs = now() - r.openAt;
      r.heldUntil = now() + r.answerSec * 1000;
      r.heldTimer = later(r, r.answerSec * 1000, () => KINDS.buzzer.judge(r, false, 'انتهى الوقت'));
      touch(true);
    },
    judge(r, ok, why) {
      if (r.state !== 'held') return;
      clearTimeout(r.heldTimer);
      const p = byId(r.holder);
      if (p) {
        const pts = ok ? r.points : -r.penalty;
        award(p, pts);
        r.log.push(row(p, pts, ok ? `✅ صح · ${fmtT(r.buzzMs)}` : `❌ ${why || 'غلط'} · ${fmtT(r.buzzMs)}`));
        r.out.add(p.id);
      }
      r.holder = null;
      r.heldUntil = null;
      if (ok) return endRound('judged');
      r.state = 'open';
      r.openAt = now();
      if (onlinePlayers().every((x) => r.out.has(x.id))) return endRound('allout');
      touch(true);
    },
    pub(r) {
      const h = byId(r.holder);
      return {
        prompt: r.prompt,
        state: r.state,
        holder: h ? { name: h.name, team: h.team } : null,
        buzzMs: r.state === 'held' ? r.buzzMs : null,
        heldUntil: r.heldUntil,
        answerSec: r.answerSec,
        outCount: r.out.size,
        answered: r.out.size,
      };
    },
    me(r, p) {
      return { status: r.out.has(p.id) ? 'out' : r.holder === p.id ? 'held' : r.state === 'held' ? 'blocked' : 'open' };
    },
    host: (r) => ({ secret: r.secretText, live: r.log }),
    finish: (r) => ({ answer: r.secretText, rows: r.log }),
  },

  // ----- bomb: pass between teams, random fuse -----
  bomb: {
    start(r) {
      r.phase = 'live';
      const ids = activeTeams();
      if (ids.length < 2) throw new Error('تحتاج لاعبين من فريقين على الأقل متصلين');
      r.turn = pick(ids);
      r.holder = randomIn(r.turn).id;
      r.passes = 0;
      r.lastPass = 0;
      later(r, rnd(r.minSec, r.maxSec) * 1000, () => endRound('boom'));
    },
    pass(r, who) {
      if (who && r.holder !== who) return;
      if (now() - r.lastPass < 400) return;
      const ids = activeTeams();
      const next = ids[(ids.indexOf(r.turn) + 1) % ids.length] ?? ids[0];
      const p = randomIn(next);
      if (!p) return;
      r.turn = next;
      r.holder = p.id;
      r.passes++;
      r.lastPass = now();
      touch(true);
    },
    pub(r) {
      const h = byId(r.holder);
      return { prompt: r.prompt, holder: h ? { name: h.name, team: h.team } : null, passes: r.passes, answered: r.passes };
    },
    me: (r, p) => ({ status: r.holder === p.id ? 'hasBomb' : 'idle' }),
    host(r) {
      const h = byId(r.holder);
      return { secret: null, live: h ? [{ name: h.name, team: h.team, detail: '💣 معه القنبلة' }] : [] };
    },
    finish(r) {
      const p = byId(r.holder);
      if (!p) return { answer: null, rows: [] };
      award(p, -10);
      return { answer: null, rows: [row(p, -10, `💥 انفجرت عنده بعد ${r.passes} تمريرات`)], boom: p.team };
    },
  },

  // ----- reaction: wait for green, early press = out -----
  reaction: {
    start(r) {
      r.phase = 'live';
      r.state = 'wait';
      later(r, rnd(r.minDelay, r.maxDelay) * 1000, () => {
        r.state = 'go';
        r.goAt = now();
        r.endsAt = r.goAt + 6000;
        later(r, 6000, () => endRound('time'));
        touch(true);
      });
    },
    press(r, p) {
      if (r.sub.has(p.id)) return;
      if (r.state === 'wait') r.sub.set(p.id, { out: true });
      else if (r.state === 'go') {
        r.sub.set(p.id, { t: now() - r.goAt });
        r.order.push(p.id);
      } else return;
      if (onlinePlayers().every((x) => r.sub.has(x.id))) endRound('done');
    },
    pub: (r) => ({ state: r.state, answered: r.sub.size }),
    me(r, p) {
      const s = r.sub.get(p.id);
      return { status: s ? (s.out ? 'out' : 'ok') : 'idle' };
    },
    host: (r) => ({
      secret: null,
      live: [...r.sub].map(([id, s]) => ({ name: byId(id)?.name, team: byId(id)?.team, detail: s.out ? '❌ مبكر' : fmtT(s.t) })),
    }),
    finish(r) {
      const rows = r.order.map((id, i) => {
        const p = byId(id);
        if (!p) return null;
        const pts = rankPts(i + 1);
        award(p, pts);
        return row(p, pts, fmtT(r.sub.get(id).t));
      }).filter(Boolean);
      for (const [id, s] of r.sub) if (s.out && byId(id)) rows.push(row(byId(id), 0, '❌ ضغط قبل الأخضر'));
      return { answer: null, rows };
    },
  },
};

function activeTeams() {
  return [...new Set(onlinePlayers().map((p) => p.team))].sort();
}

const EMO = ['🍎', '🐘', '🚗', '🔑', '🌙', '🎸', '⚽', '☕', '🐱', '🍕', '🚀', '🌵', '🎈', '📚', '🐢', '🍩', '🦁', '🌹', '🔔', '🎩', '🐟', '🍉'];

const GAMES = {
  type: {
    kind: 'race',
    title: '⚡ أسرع واحد يكتب',
    build(o) {
      const text = str(o.text) || pick(BANK.type);
      return { prompt: 'اكتب الجملة التالية بأسرع وقت', display: text, strict: true, answers: [text], secretText: text, duration: num(o.duration, 30, 5, 300) };
    },
  },
  scramble: {
    kind: 'race',
    title: '🧠 فك الكلمة',
    build(o) {
      const word = str(o.word, 30).replace(/\s+/g, '') || pick(BANK.scramble);
      const letters = Array.from(word);
      let tiles = shuffle(letters);
      for (let i = 0; i < 20 && tiles.join('') === word && letters.length > 1; i++) tiles = shuffle(letters);
      return { prompt: 'رتّب الحروف لتكوين كلمة', tiles, answers: [word], secretText: word, duration: num(o.duration, 40, 5, 300) };
    },
  },
  fill: {
    kind: 'race',
    title: '🔥 اكمل الجملة',
    build(o) {
      const b = o.prompt ? { prompt: str(o.prompt), answer: str(o.answer) } : pick(BANK.fill);
      const answers = String(b.answer).split('|').map((s) => s.trim()).filter(Boolean);
      if (!answers.length) throw new Error('أدخل الإجابة');
      return { prompt: 'اكمل الجملة', display: b.prompt, answers, secretText: answers.join(' / '), duration: num(o.duration, 30, 5, 300) };
    },
  },
  memory: {
    kind: 'race',
    title: '👀 Memory Flash',
    build(o) {
      const n = num(o.count, 9, 5, 12);
      const items = shuffle(EMO).slice(0, n);
      let prompt, answer;
      if (Math.random() < 0.5) {
        const k = Math.floor(Math.random() * n);
        prompt = `ما العنصر رقم ${k + 1}؟`;
        answer = items[k];
      } else {
        const k = Math.floor(Math.random() * (n - 1));
        prompt = `ما العنصر الذي ظهر بعد ${items[k]} ؟`;
        answer = items[k + 1];
      }
      const options = shuffle([answer, ...shuffle(items.filter((x) => x !== answer)).slice(0, 3)]);
      return { prompt, options, answers: [answer], secretText: answer, flash: { items, ms: num(o.showSec, 4, 1, 15) * 1000 }, duration: num(o.duration, 15, 5, 120), strict: true };
    },
  },
  closest: {
    kind: 'closest',
    title: '🎯 أقرب إجابة',
    build(o) {
      const b = o.prompt ? { prompt: str(o.prompt), answer: parseNum(o.answer), unit: str(o.unit, 10) } : pick(BANK.closest);
      if (!Number.isFinite(Number(b.answer))) throw new Error('الإجابة يجب أن تكون رقماً');
      return { prompt: b.prompt, target: Number(b.answer), unit: b.unit || '', secretText: fmtN(b.answer) + (b.unit || ''), duration: num(o.duration, 30, 5, 300) };
    },
  },
  buzzer: {
    kind: 'buzzer',
    title: '🔴 The Buzzer',
    build(o) {
      const b = o.prompt ? { prompt: str(o.prompt), answer: str(o.answer) } : pick(BANK.buzzer);
      return { prompt: b.prompt, secretText: b.answer, answerSec: num(o.answerSec, 5, 2, 30), points: num(o.points, 10, 1, 100), penalty: num(o.penalty, 5, 0, 100), duration: num(o.duration, 90, 10, 600) };
    },
  },
  bomb: {
    kind: 'bomb',
    title: '💣 القنبلة',
    build(o) {
      const minSec = num(o.minSec, 5, 2, 60);
      return { prompt: str(o.prompt) || pick(BANK.bomb), minSec, maxSec: Math.max(minSec + 1, num(o.maxSec, 12, 3, 90)) };
    },
  },
  reaction: {
    kind: 'reaction',
    title: '😈 لا تضغط الزر',
    build(o) {
      const minDelay = num(o.minDelay, 2, 1, 20);
      return { minDelay, maxDelay: Math.max(minDelay + 1, num(o.maxDelay, 6, 2, 30)) };
    },
  },
};

function startRound(game, params) {
  if (G.round) throw new Error('هناك جولة جارية، أنهِها أولاً');
  const def = GAMES[game];
  if (!def) throw new Error('لعبة غير معروفة');
  if (onlinePlayers().length < 1) throw new Error('لا يوجد لاعبون متصلون');
  const r = {
    id: ++roundSeq,
    game,
    kind: def.kind,
    title: def.title,
    phase: 'live',
    startedAt: now(),
    timers: [],
    sub: new Map(),
    order: [],
    startScores: [...G.teamScores],
    ...def.build(params || {}),
  };
  if (r.answers) r.answers = r.answers.map((a) => norm(a, r.strict));
  G.round = r;
  G.phase = 'round';
  try {
    KINDS[r.kind].start(r);
  } catch (e) {
    clearTimers(r);
    G.round = null;
    G.phase = 'lobby';
    throw e;
  }
  touch(true);
}
const clearTimers = (r) => r.timers.forEach(clearTimeout);

function endRound(reason) {
  const r = G.round;
  if (!r) return;
  clearTimers(r);
  const res = KINDS[r.kind].finish(r) || { rows: [] };
  G.last = {
    game: r.game,
    title: r.title,
    kind: r.kind,
    prompt: r.display || r.prompt || null,
    answer: res.answer ?? null,
    rows: res.rows,
    boom: res.boom ?? null,
    reason,
    teamDelta: G.teamScores.map((s, i) => s - r.startScores[i]),
  };
  G.history.push({ game: r.game, title: r.title });
  G.round = null;
  G.phase = 'results';
  touch(true);
}

// ───────────── views ─────────────
function publicRound(r) {
  return {
    id: r.id,
    game: r.game,
    kind: r.kind,
    title: r.title,
    phase: r.phase,
    until: r.nextAt || null,
    from: r.liveAt || r.startedAt,
    endsAt: r.endsAt || null,
    total: onlinePlayers().length,
    ...KINDS[r.kind].pub(r),
  };
}
function pub() {
  const all = allPlayers();
  return {
    now: now(),
    event: G.event,
    phase: G.phase,
    joinUrl: joinUrl(),
    teams: TEAMS.slice(0, G.teamCount).map((t) => ({ ...t, score: G.teamScores[t.id], count: all.filter((p) => p.team === t.id).length })),
    online: onlinePlayers().length,
    players: G.phase === 'lobby' ? all.map((p) => ({ n: p.name, t: p.team, o: p.online })) : undefined,
    top: [...all].sort((a, b) => b.score - a.score).slice(0, 5).map((p) => ({ n: p.name, t: p.team, s: p.score })),
    round: G.round ? publicRound(G.round) : null,
    last: G.phase === 'results' || G.phase === 'final' ? G.last : null,
    final: G.final,
    roundNo: G.history.length,
  };
}
function meFor(p) {
  const r = G.round;
  const L = G.phase === 'results' ? G.last?.rows.find((x) => x.id === p.id) : null;
  return {
    joined: true,
    id: p.id,
    name: p.name,
    team: p.team,
    score: p.score,
    st: r ? KINDS[r.kind].me(r, p) || {} : {},
    last: G.phase === 'results' ? L || { pts: 0 } : null,
  };
}
function hostView() {
  const r = G.round;
  return {
    ips: IPS,
    ip: G.ip,
    joinUrl: joinUrl(),
    teamCount: G.teamCount,
    players: allPlayers().map((p) => ({ id: p.id, name: p.name, team: p.team, score: p.score, online: p.online })),
    ...(r ? KINDS[r.kind].host(r) : {}),
  };
}

let tmr = null;
function touch(immediate) {
  if (immediate) return flush();
  if (tmr) return;
  tmr = setTimeout(flush, 60);
}
function flush() {
  if (tmr) clearTimeout(tmr);
  tmr = null;
  const s = pub();
  io.to('screen').to('host').to('anon').emit('state', s);
  io.to('host').emit('hstate', hostView());
  for (const p of G.players.values()) {
    if (p.online && p.sid) {
      io.to(p.sid).emit('state', s);
      io.to(p.sid).emit('me', meFor(p));
    }
  }
}

// ───────────── server ─────────────
const app = express();
const server = http.createServer(app);
const io = new Server(server, { pingInterval: 5000, pingTimeout: 8000 });

app.use(express.static(path.join(__dirname, 'public'), { extensions: ['html'] }));
app.get('/', (_q, s) => s.sendFile(path.join(__dirname, 'public', 'play.html')));
app.get('/api/bank', (_q, s) => s.json(BANK));
app.get('/api/qr', async (_q, s) => {
  s.type('image/png').send(await QRCode.toBuffer(joinUrl(), { margin: 1, width: 600, errorCorrectionLevel: 'M' }));
});

io.on('connection', (sock) => {
  const a = sock.handshake.auth || {};

  if (a.role === 'screen') {
    sock.join('screen');
    return sock.emit('state', pub());
  }

  if (a.role === 'host') {
    if (!(a.key === HOST_KEY || isLocal(sock.handshake.address))) {
      sock.emit('denied');
      return sock.disconnect(true);
    }
    sock.join('host');
    const H = (ev, fn) =>
      sock.on(ev, (d, cb) => {
        try {
          fn(d || {});
          cb && cb({ ok: true });
        } catch (e) {
          cb && cb({ ok: false, err: e.message });
        }
        touch(true);
      });
    H('start', (d) => startRound(d.game, d.params));
    H('end', () => endRound('host'));
    H('lobby', () => {
      if (G.round) throw new Error('أنهِ الجولة أولاً');
      G.phase = 'lobby';
      G.final = null;
    });
    H('config', (d) => {
      if (d.event != null) G.event = str(d.event, 40) || 'PLAYROOM';
      if (d.teamCount != null) {
        G.teamCount = num(d.teamCount, 2, 2, 4);
        for (const p of allPlayers()) if (p.team >= G.teamCount) p.team = smallestTeam();
      }
      if (d.ip && IPS.some((i) => i.address === d.ip)) G.ip = d.ip;
    });
    H('adjust', (d) => {
      const t = num(d.team, 0, 0, G.teamCount - 1);
      G.teamScores[t] += num(d.delta, 0, -1000, 1000);
    });
    H('shuffle', () => {
      shuffle(allPlayers()).forEach((p, i) => (p.team = i % G.teamCount));
    });
    H('setTeam', (d) => {
      const p = byId(d.id);
      if (p) p.team = num(d.team, 0, 0, G.teamCount - 1);
    });
    H('kick', (d) => {
      const p = byId(d.id);
      if (!p) return;
      G.players.delete(p.token);
      if (p.sid) io.to(p.sid).emit('kicked');
    });
    H('judge', (d) => {
      const r = G.round;
      if (r?.kind === 'buzzer') KINDS.buzzer.judge(r, !!d.ok);
    });
    H('bombPass', () => {
      const r = G.round;
      if (r?.kind === 'bomb') KINDS.bomb.pass(r);
    });
    H('final', () => {
      if (G.round) endRound('host');
      const max = Math.max(...G.teamScores.slice(0, G.teamCount));
      G.final = { winners: G.teamScores.slice(0, G.teamCount).map((s, i) => (s === max ? i : -1)).filter((i) => i >= 0), score: max };
      G.phase = 'final';
    });
    H('reset', () => {
      if (G.round) {
        clearTimers(G.round);
        G.round = null;
      }
      G.teamScores = [0, 0, 0, 0];
      allPlayers().forEach((p) => (p.score = 0));
      G.history = [];
      G.last = null;
      G.final = null;
      G.phase = 'lobby';
    });
    sock.emit('state', pub());
    return sock.emit('hstate', hostView());
  }

  // ----- player -----
  const token = str(a.pid, 64);
  let p = token && G.players.get(token);
  const attach = () => {
    p.sid = sock.id;
    p.online = true;
    sock.leave('anon');
    touch(true);
  };
  if (p) attach();
  else {
    sock.join('anon');
    sock.emit('state', pub());
    sock.emit('me', { joined: false });
  }

  sock.on('join', (d, cb) => {
    const name = str(d?.name, 20);
    if (!token || !name) return cb && cb({ ok: false, err: 'اكتب اسمك' });
    p = G.players.get(token);
    if (p) p.name = name;
    else {
      p = { id: crypto.randomBytes(4).toString('hex'), token, name, team: smallestTeam(), score: 0, online: true, sid: sock.id };
      G.players.set(token, p);
    }
    attach();
    cb && cb({ ok: true });
  });

  sock.on('answer', (v, cb) => {
    const r = G.round;
    if (!p || !r || !KINDS[r.kind].submit) return cb && cb('locked');
    const res = KINDS[r.kind].submit(r, p, v);
    touch();
    cb && cb(res);
  });
  sock.on('buzz', () => {
    const r = G.round;
    if (p && r?.kind === 'buzzer') KINDS.buzzer.buzz(r, p);
  });
  sock.on('press', () => {
    const r = G.round;
    if (!p || !r) return;
    if (r.kind === 'reaction') {
      KINDS.reaction.press(r, p);
      touch();
    }
  });
  sock.on('pass', () => {
    const r = G.round;
    if (p && r?.kind === 'bomb') KINDS.bomb.pass(r, p.id);
  });

  sock.on('disconnect', () => {
    if (p && p.sid === sock.id) {
      p.online = false;
      const r = G.round;
      if (r?.kind === 'bomb' && r.holder === p.id) KINDS.bomb.pass(r);
      touch();
    }
  });
});

server.listen(PORT, '0.0.0.0', () => {
  const line = '─'.repeat(54);
  console.log(`\n${line}\n  PLAYROOM — Live Event Games\n${line}`);
  console.log(`  شاشة المضيف  : http://localhost:${PORT}/host`);
  console.log(`  الشاشة الكبيرة: http://localhost:${PORT}/screen`);
  console.log(`  رابط اللاعبين : ${joinUrl()}   (يظهر في QR)`);
  if (IPS.length > 1) console.log(`  عناوين أخرى   : ${IPS.map((i) => `${i.address} (${i.name})`).join(' | ')}`);
  console.log(`  مفتاح المضيف  : ${HOST_KEY}  → http://${G.ip}:${PORT}/host?key=${HOST_KEY}`);
  console.log(`${line}\n`);
});
