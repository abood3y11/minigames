@echo off
chcp 65001 >nul
if not exist node_modules call npm install
node server.js
pause
