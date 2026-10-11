// Shared client helpers
const TEAM_FALLBACK = ['#ef4444', '#3b82f6', '#22c55e', '#eab308'];
let clockOffset = 0;
const sNow = () => Date.now() + clockOffset;
const esc = (s) => String(s ?? '').replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const $ = (s, el = document) => el.querySelector(s);
const tcolor = (t) => TEAM_FALLBACK[t] || '#888';
const MEDAL = ['🥇', '🥈', '🥉'];

function connect(auth, on) {
  const sock = io({ auth, transports: ['websocket', 'polling'], reconnectionDelay: 500, reconnectionDelayMax: 2000 });
  sock.on('state', (s) => {
    clockOffset = s.now - Date.now();
  });
  for (const [k, f] of Object.entries(on)) sock.on(k, f);
  return sock;
}

// Drives every .tm (text) and .fill (bar) element from data-until / data-from / data-to (server ms)
function runTimers(extra) {
  const tick = () => {
    const t = sNow();
    document.querySelectorAll('[data-until]').forEach((el) => {
      const until = +el.dataset.until;
      const left = Math.max(0, until - t);
      if (el.dataset.mode === 'int') el.textContent = Math.max(1, Math.ceil(left / 1000));
      else el.textContent = (left / 1000).toFixed(1);
      if (el.dataset.mode === 'int' && el.dataset.last !== el.textContent) {
        el.dataset.last = el.textContent;
        extra && extra('tick', el.textContent);
      }
    });
    document.querySelectorAll('[data-bar]').forEach((el) => {
      const [from, to] = el.dataset.bar.split(',').map(Number);
      const p = Math.min(1, Math.max(0, (to - t) / (to - from)));
      el.firstElementChild.style.width = p * 100 + '%';
      el.classList.toggle('hot', p < 0.25);
    });
    requestAnimationFrame(tick);
  };
  tick();
}
