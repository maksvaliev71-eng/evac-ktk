// Сервер «Эвакуация КТК». Без внешних зависимостей, нужен Node.js 18 или новее.
// Запуск: node server.js   (порт и папка данных задаются переменными PORT и DATA_DIR)
"use strict";
const http = require("http"), fs = require("fs"), path = require("path"), crypto = require("crypto"), zlib = require("zlib"), net = require("net"), tls = require("tls");

const PORT = parseInt(process.env.PORT || "8080", 10);
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(__dirname, "data"));
const APP_DIR = path.join(DATA_DIR, "app");
fs.mkdirSync(APP_DIR, { recursive: true });
const INDEX = fs.existsSync(path.join(__dirname, "index.html")) ? path.join(__dirname, "index.html") : path.join(__dirname, "public", "index.html");

const DEFAULT_PERMS = {
  vnutriros: ["plan_vnutriros", "fact_vnutriros"],
  export: ["plan_export", "fact_export"],
  import: ["import"],
  rail: ["routes"],
};
const DEPT_KEYS = ["vnutriros", "export", "import", "rail"];
const ALL_DEPTS = DEPT_KEYS.concat(["viewer", "manager", "admin"]);

// ---------- файловое хранилище ----------
function readJson(file, def) { try { return JSON.parse(fs.readFileSync(file, "utf8")); } catch (e) { return def; } }
function writeJson(file, obj) {
  const tmp = file + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(obj));
  fs.renameSync(tmp, file);
}
const USERS_F = path.join(DATA_DIR, "users.json"), PERMS_F = path.join(DATA_DIR, "perms.json"), LOG_F = path.join(DATA_DIR, "log.json");
let users = readJson(USERS_F, {});      // id -> {login,name,dept,salt,iter,hash}
let perms = readJson(PERMS_F, null);    // {map}
let logs = readJson(LOG_F, []);
const EXT_F = path.join(DATA_DIR, "ext.json"), MAIL_F = path.join(DATA_DIR, "mail.json"), BK_DIR = path.join(DATA_DIR, "backups");
let ext = readJson(EXT_F, {});          // статусы готовности, сроки, комментарии
ext.status = ext.status || {}; ext.deadlines = ext.deadlines || {}; ext.comments = ext.comments || []; ext.reminded = ext.reminded || {};
const MAIL_DEF = { enabled: false, mode: "ssl", host: "", port: 465, user: "", pass: "", from: "", siteUrl: "", evReady: true, evAll: true, evClosed: true, evRemind: true };
let mailCfg = Object.assign({}, MAIL_DEF, readJson(MAIL_F, {}));
const HIST_F = path.join(DATA_DIR, "history.jsonl");
let history = [];   // последние правки по ячейкам: {t,u,n,d,doc,p,f,v}
try { history = fs.readFileSync(HIST_F, "utf8").split("\n").filter(Boolean).slice(-8000).map(l => { try { return JSON.parse(l); } catch (e) { return null; } }).filter(Boolean); fs.writeFileSync(HIST_F, history.map(h => JSON.stringify(h)).join("\n") + (history.length ? "\n" : "")); } catch (e) { history = []; }
const appDocs = {};
for (const f of fs.readdirSync(APP_DIR)) { if (f.endsWith(".json")) appDocs[f.slice(0, -5)] = readJson(path.join(APP_DIR, f), {}); }

// ---------- пароли и сессии ----------
const ITER = 150000;
function hashPw(pw, salt) { return crypto.pbkdf2Sync(pw, Buffer.from(salt, "hex"), ITER, 32, "sha256").toString("hex"); }
function loginId(login) { return "u_" + Buffer.from(String(login).trim().toLowerCase(), "utf8").toString("hex"); }
function makeUser(login, name, dept, pw) {
  const salt = crypto.randomBytes(16).toString("hex");
  return { login: String(login).trim(), name: String(name || login).trim(), dept, salt, iter: ITER, hash: hashPw(pw, salt) };
}
const sessions = new Map(); // token -> userId
function newSession(uid) { const t = crypto.randomBytes(32).toString("hex"); sessions.set(t, uid); return t; }
function parseCookies(req) {
  const o = {}; (req.headers.cookie || "").split(";").forEach(p => { const i = p.indexOf("="); if (i > 0) o[p.slice(0, i).trim()] = p.slice(i + 1).trim(); });
  return o;
}
function sessionUser(req) {
  const t = parseCookies(req).evac_sid; const uid = t && sessions.get(t);
  if (!uid || !users[uid]) return null;
  return { id: uid, login: users[uid].login, name: users[uid].name, dept: users[uid].dept };
}
const attempts = new Map();
function tooMany(ip) {
  const now = Date.now(), a = (attempts.get(ip) || []).filter(t => now - t < 60000);
  a.push(now); attempts.set(ip, a); return a.length > 10;
}

// ---------- права ----------
function permsFor(dept) { return (perms && perms.map && perms.map[dept]) || DEFAULT_PERMS[dept] || []; }
function areaOfDoc(id) { return /^a\d{3}$/.test(id) ? "archive" : id; }
function canWriteDoc(me, id) {
  if (me.dept === "admin") return true;
  const a = areaOfDoc(id);
  if (a === "archive" || a === "meta") return false;
  if (a.indexOf("reasons_") === 0) return a === "reasons_" + me.dept;
  return permsFor(me.dept).includes(a);
}
// какой части статуса соответствует область данных
const AREA_KIND = {
  plan_vnutriros: { dept: "vnutriros", kind: "plan" }, fact_vnutriros: { dept: "vnutriros", kind: "fact" },
  plan_export: { dept: "export", kind: "plan" }, fact_export: { dept: "export", kind: "fact" },
  import: { dept: "import", kind: "import" }, routes: { dept: "rail", kind: "rail" },
};
const STATUS_KINDS = { vnutriros: ["plan", "fact"], export: ["plan", "fact"], expl: ["plan"], import: ["import"], rail: ["rail", "railfact"] };
const KIND_LABEL = { plan: "план", fact: "факт", import: "сдача импорта", rail: "поезда: ТЕУ, план, доли", railfact: "поезда: факт" };
const DEPT_LABEL = { vnutriros: "Внутрироссийский", export: "Экспортный", expl: "Эксплуатация", import: "Импорт", rail: "ЖД отдел", viewer: "Отчётность", manager: "Руководитель", admin: "Администратор" };
function mskToday() { return new Date(Date.now() + 3 * 3600000).toISOString().slice(0, 10); }
function mskHour() { return new Date(Date.now() + 3 * 3600000).getUTCHours(); }
function deadlineLocked(kind) {
  const d = ext.deadlines[kind]; if (!d || !/^\d{4}-\d{2}-\d{2}$/.test(d)) return false;
  return Date.now() > Date.parse(d + "T23:59:59+03:00");
}
function fmtDate(d) { const m = String(d).match(/^(\d{4})-(\d{2})-(\d{2})$/); return m ? m[3] + "." + m[2] + "." + m[1] : d; }
function writeDenied(me, id) {
  if (!canWriteDoc(me, id)) return "Нет прав на изменение этой части данных";
  if (me.dept !== "admin") { const ak = AREA_KIND[areaOfDoc(id)]; if (ak && deadlineLocked(ak.kind)) return "Срок внесения истёк (" + fmtDate(ext.deadlines[ak.kind]) + "). Обратитесь к администратору"; }
  return null;
}
function saveExt() { writeJson(EXT_F, ext); broadcast("ext", {}); }
function publicExt(me) { return { status: ext.status, deadlines: ext.deadlines, comments: (me && (me.dept === "admin" || me.dept === "manager")) ? ext.comments : [] }; }

// ---------- события (SSE) ----------
const clients = new Set();
function broadcast(event, data) {
  const msg = "event: " + event + "\ndata: " + JSON.stringify(data) + "\n\n";
  for (const c of clients) { try { c.res.write(msg); } catch (e) {} }
}
function addLog(me, id) {
  const now = Date.now(), area = areaOfDoc(id);
  const last = logs[0];
  if (last && last.u === me.id && last.a[0] === area && now - last.t < 5 * 60000) last.t = now;
  else logs.unshift({ t: now, u: me.id, n: me.name, d: me.dept, a: [area] });
  logs = logs.slice(0, 500); writeJson(LOG_F, logs);
  broadcast("log", {});
}
function addLogText(me, text) {
  logs.unshift({ t: Date.now(), u: me.id, n: me.name, d: me.dept, a: [text] });
  logs = logs.slice(0, 500); writeJson(LOG_F, logs); broadcast("log", {});
}

// ---------- история правок по ячейкам ----------
function flatten(v, pre, out) {
  if (v && typeof v === "object") { for (const k of Object.keys(v)) flatten(v[k], pre ? pre + "." + k : k, out); }
  else out[pre] = v;
  return out;
}
function recordHistory(me, doc, before, after) {
  if (doc === "meta") return;
  const a = flatten(before || {}, "", {}), b = flatten(after || {}, "", {}), ch = [], t = Date.now();
  for (const k of new Set(Object.keys(a).concat(Object.keys(b)))) {
    if (doc === "forecast" && /^log(\.|$)/.test(k)) continue;
    const x = a[k], y = b[k];
    if (x === y || (x === undefined && (y === 0 || y === "")) || (y === undefined && (x === 0 || x === ""))) continue;
    ch.push({ t, u: me.id, n: me.name, d: me.dept, doc, p: k, f: x === undefined ? null : x, v: y === undefined ? null : y });
  }
  if (!ch.length) return;
  const rows = ch.length > 300 ? [{ t, u: me.id, n: me.name, d: me.dept, doc, p: "*", f: null, v: null, c: ch.length }] : ch;
  fs.appendFileSync(HIST_F, rows.map(h => JSON.stringify(h)).join("\n") + "\n");
  history.push(...rows);
  if (history.length > 10000) { history = history.slice(-8000); fs.writeFileSync(HIST_F, history.map(h => JSON.stringify(h)).join("\n") + "\n"); }
}

// ---------- почта (SMTP без внешних библиотек) ----------
const mailLog = [];
function b64(str) { return Buffer.from(String(str), "utf8").toString("base64"); }
function addrOnly(a) { const m = String(a).match(/<([^>]+)>/); return (m ? m[1] : String(a)).trim(); }
function smtpSend(cfg, rcpts, subject, text) {
  return new Promise((resolve, reject) => {
    let sock, buf = "", lines = [], queue = [], waiter = null, finished = false;
    const fail = e => { if (finished) return; finished = true; clearTimeout(timer); try { sock && sock.destroy(); } catch (x) {} reject(e instanceof Error ? e : new Error(String(e))); };
    const timer = setTimeout(() => fail(new Error("Таймаут: почтовый сервер не отвечает")), 25000);
    function onData(d) {
      buf += d; let i;
      while ((i = buf.indexOf("\n")) >= 0) {
        const ln = buf.slice(0, i).replace(/\r$/, ""); buf = buf.slice(i + 1); lines.push(ln);
        if (/^\d{3}( |$)/.test(ln)) { const r = { code: parseInt(ln.slice(0, 3), 10), text: lines.join(" | ") }; lines = []; if (waiter) { const w = waiter; waiter = null; w(r); } else queue.push(r); }
      }
    }
    const read = () => new Promise(res => { if (queue.length) res(queue.shift()); else waiter = res; });
    function attach(s) { sock = s; s.setEncoding("utf8"); s.on("data", onData); s.on("error", fail); s.on("close", () => fail(new Error("Почтовый сервер закрыл соединение"))); }
    const cmd = async (c, ok) => { sock.write(c + "\r\n"); const r = await read(); if (!ok.includes(r.code)) throw new Error("Почтовый сервер ответил: " + r.text.slice(0, 200)); return r; };
    (async () => {
      const port = parseInt(cfg.port, 10) || (cfg.mode === "ssl" ? 465 : 587);
      if (cfg.mode === "ssl") {
        await new Promise((res, rej) => { const s = tls.connect({ host: cfg.host, port, servername: cfg.host }, res); s.once("error", rej); attach(s); });
      } else {
        await new Promise((res, rej) => { const s = net.connect({ host: cfg.host, port }, res); s.once("error", rej); attach(s); });
      }
      let g = await read(); if (g.code !== 220) throw new Error("Почтовый сервер ответил: " + g.text.slice(0, 200));
      await cmd("EHLO evac.local", [250]);
      if (cfg.mode === "starttls") {
        await cmd("STARTTLS", [220]);
        const raw = sock; raw.removeAllListeners("data"); raw.removeAllListeners("close"); raw.removeAllListeners("error");
        buf = ""; lines = []; queue = [];
        await new Promise((res, rej) => { const s = tls.connect({ socket: raw, servername: cfg.host }, res); s.once("error", rej); attach(s); raw.on("error", fail); });
        await cmd("EHLO evac.local", [250]);
      }
      if (cfg.user) { await cmd("AUTH LOGIN", [334]); await cmd(b64(cfg.user), [334]); await cmd(b64(cfg.pass || ""), [235]); }
      const from = cfg.from || cfg.user;
      await cmd("MAIL FROM:<" + addrOnly(from) + ">", [250]);
      for (const r of rcpts) await cmd("RCPT TO:<" + addrOnly(r) + ">", [250, 251]);
      await cmd("DATA", [354]);
      const hdr = ["From: " + from, "To: " + rcpts.join(", "), "Subject: =?UTF-8?B?" + b64(subject) + "?=", "Date: " + new Date().toUTCString(),
        "Message-ID: <" + crypto.randomBytes(8).toString("hex") + "@evac.local>", "MIME-Version: 1.0", "Content-Type: text/plain; charset=utf-8", "Content-Transfer-Encoding: base64"].join("\r\n");
      const body = b64(text).replace(/.{1,76}/g, "$&\r\n");
      sock.write(hdr + "\r\n\r\n" + body + ".\r\n");
      const d = await read(); if (d.code !== 250) throw new Error("Почтовый сервер не принял письмо: " + d.text.slice(0, 200));
      try { sock.write("QUIT\r\n"); } catch (x) {}
      finished = true; clearTimeout(timer); try { sock.end(); } catch (x) {}
      resolve();
    })().catch(fail);
  });
}
function mailErrText(e) {
  const m = String((e && e.message) || e), c = e && e.code;
  if (/\b53[45]\b|Authentication|auth/i.test(m)) return m + ". Почта не приняла логин или пароль. Для Mail.ru нужен «пароль для внешнего приложения», а не обычный пароль от ящика.";
  if (c === "ETIMEDOUT" || /Таймаут/.test(m)) return "Нет связи с почтовым сервером (таймаут). Возможно, хостинг блокирует исходящий порт " + (mailCfg.port || "") + ". Попробуйте другой порт или режим (SSL 465 / STARTTLS 587).";
  if (c === "ECONNREFUSED") return "Почтовый сервер отклонил соединение (порт " + (mailCfg.port || "") + " закрыт). Проверьте адрес сервера и порт.";
  if (c === "ENOTFOUND" || c === "EAI_AGAIN") return "Адрес почтового сервера не найден: " + (mailCfg.host || "") + ".";
  return m;
}
let mailChain = Promise.resolve();
function sendMail(rcpts, subject, text) {
  rcpts = [...new Set(rcpts.filter(Boolean))];
  if (!mailCfg.enabled || !mailCfg.host || !rcpts.length) return mailChain;
  const full = (mailCfg.siteUrl ? text + "\n\n" + mailCfg.siteUrl : text);
  mailChain = mailChain.then(() => smtpSend(mailCfg, rcpts, "[Эвакуация КТК] " + subject, full)
    .then(() => { mailLog.unshift({ t: Date.now(), to: rcpts.join(", "), s: subject, ok: true }); })
    .catch(e => { mailLog.unshift({ t: Date.now(), to: rcpts.join(", "), s: subject, ok: false, err: mailErrText(e) }); }))
    .then(() => { mailLog.length = Math.min(mailLog.length, 30); });
  return mailChain;
}
function emailsOf(pred) { return Object.values(users).filter(u => u.email && pred(u)).map(u => u.email); }
const mailAdmins = (subj, text) => sendMail(emailsOf(u => u.dept === "admin"), subj, text);
const mailAll = (subj, text) => sendMail(emailsOf(() => true), subj, text);
const mailDept = (dept, subj, text) => sendMail(emailsOf(u => u.dept === dept), subj, text);

// ---------- автоматические резервные копии ----------
function backupList() {
  try { return fs.readdirSync(BK_DIR).filter(f => /^evac-[0-9a-z-]{4,40}\.json$/.test(f)).map(f => { const st = fs.statSync(path.join(BK_DIR, f)); return { name: f, t: st.mtimeMs, size: st.size }; }).sort((a, b) => b.t - a.t); } catch (e) { return []; }
}
function makeBackup(tag) {
  fs.mkdirSync(BK_DIR, { recursive: true });
  const name = "evac-" + mskToday() + (tag ? "-" + tag : "") + ".json";
  writeJson(path.join(BK_DIR, name), { version: 1, t: Date.now(), docs: appDocs, perms, ext, users });
  const all = backupList(), daily = all.filter(f => !/^evac-\d{4}-\d{2}-\d{2}-/.test(f.name)), pre = all.filter(f => /^evac-\d{4}-\d{2}-\d{2}-/.test(f.name));
  daily.slice(30).concat(pre.slice(10)).forEach(f => { try { fs.unlinkSync(path.join(BK_DIR, f.name)); } catch (e) {} });
  return name;
}
function dailyBackup() { try { if (!fs.existsSync(path.join(BK_DIR, "evac-" + mskToday() + ".json")) && Object.keys(users).length) makeBackup(""); } catch (e) { console.error("backup:", e.message); } }
function restoreBackup(name) {
  const b = readJson(path.join(BK_DIR, name), null);
  if (!b || !b.docs) throw new Error("Копия повреждена");
  makeBackup("pre-restore");
  for (const f of fs.readdirSync(APP_DIR)) { try { fs.unlinkSync(path.join(APP_DIR, f)); } catch (e) {} }
  for (const k of Object.keys(appDocs)) delete appDocs[k];
  for (const id of Object.keys(b.docs)) { if (!/^[A-Za-z0-9_]{1,40}$/.test(id)) continue; appDocs[id] = b.docs[id]; writeJson(path.join(APP_DIR, id + ".json"), b.docs[id]); }
  if (b.perms) { perms = b.perms; writeJson(PERMS_F, perms); }
  if (b.ext) { ext = Object.assign({ status: {}, deadlines: {}, comments: [], reminded: {} }, b.ext); writeJson(EXT_F, ext); }
  broadcast("reload", {});
}

// ---------- напоминания о сроках ----------
function remindersCheck() {
  if (!mailCfg.enabled || !mailCfg.evRemind || mskHour() < 9) return;
  const today = mskToday(), tomorrow = new Date(Date.now() + 3 * 3600000 + 86400000).toISOString().slice(0, 10);
  let dirty = false;
  for (const dept of Object.keys(STATUS_KINDS)) for (const kind of STATUS_KINDS[dept]) {
    const d = ext.deadlines[kind === "railfact" ? "rail" : kind]; if (!d || (d !== today && d !== tomorrow)) continue;
    const st = ext.status[dept] && ext.status[dept][kind]; if (st && st.ready && !st.dirty) continue;
    const key = dept + "|" + kind + "|" + d + "|" + today; if (ext.reminded[key]) continue;
    ext.reminded[key] = 1; dirty = true;
    mailDept(dept, "Напоминание: срок — " + KIND_LABEL[kind], "Срок внесения («" + KIND_LABEL[kind] + "») — " + fmtDate(d) + (d === today ? " (сегодня)" : " (завтра)") + ". Данные ещё не подтверждены кнопкой «Готово».");
  }
  Object.keys(ext.reminded).forEach(k => { if (k.split("|")[3] < today) delete ext.reminded[k]; });
  if (dirty) writeJson(EXT_F, ext);
}
function allReady() {
  return Object.keys(STATUS_KINDS).every(d => STATUS_KINDS[d].every(k => { const s = ext.status[d] && ext.status[d][k]; return s && s.ready && !s.dirty; }));
}

// ---------- HTTP ----------
function send(res, code, obj, headers) {
  const body = typeof obj === "string" ? obj : JSON.stringify(obj);
  const h = Object.assign({ "Content-Type": typeof obj === "string" ? "text/html; charset=utf-8" : "application/json; charset=utf-8", "Cache-Control": "no-store", "X-Content-Type-Options": "nosniff", "Vary": "Accept-Encoding" }, headers || {});
  const ae = String((res.req && res.req.headers["accept-encoding"]) || "");
  if (body.length > 1024 && /\bgzip\b/.test(ae)) {
    h["Content-Encoding"] = "gzip";
    const gz = zlib.gzipSync(body, { level: 6 });
    h["Content-Length"] = gz.length;
    res.writeHead(code, h); return res.end(gz);
  }
  res.writeHead(code, h);
  res.end(body);
}
function readBody(req, limit) {
  return new Promise((resolve, reject) => {
    let n = 0; const chunks = [];
    req.on("data", c => { n += c.length; if (n > limit) { reject(new Error("too large")); req.destroy(); } else chunks.push(c); });
    req.on("end", () => { try { resolve(chunks.length ? JSON.parse(Buffer.concat(chunks).toString("utf8")) : {}); } catch (e) { reject(new Error("bad json")); } });
    req.on("error", reject);
  });
}
function publicUsers(withEmail) {
  const o = {}; for (const id of Object.keys(users)) { o[id] = { login: users[id].login, name: users[id].name, dept: users[id].dept }; if (withEmail) o[id].email = users[id].email || ""; } return o;
}
function cookieHeader(req, token, maxAge) {
  const secure = (req.headers["x-forwarded-proto"] === "https") ? "; Secure" : "";
  return "evac_sid=" + token + "; HttpOnly; SameSite=Lax; Path=/; Max-Age=" + maxAge + secure;
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, "http://x"); const p = url.pathname;
  try {
    if (req.method === "GET" && (p === "/" || p === "/index.html")) {
      const html = fs.readFileSync(INDEX, "utf8");
      const etag = '"' + crypto.createHash("md5").update(html).digest("hex") + '"';
      if (req.headers["if-none-match"] === etag) { res.writeHead(304, { "ETag": etag, "Cache-Control": "no-cache" }); return res.end(); }
      return send(res, 200, html, { "ETag": etag, "Cache-Control": "no-cache" });
    }
    if (!p.startsWith("/api/")) return send(res, 404, { error: "Не найдено" });
    const ip = req.socket.remoteAddress || "";
    const me = sessionUser(req);

    if (p === "/api/status" && req.method === "GET") return send(res, 200, { setup: Object.keys(users).length === 0, me });
    if (p === "/api/setup" && req.method === "POST") {
      if (Object.keys(users).length) return send(res, 403, { error: "Администратор уже создан" });
      const b = await readBody(req, 10000);
      if (!b.login || String(b.login).length > 40 || !b.password || String(b.password).length < 6) return send(res, 400, { error: "Логин до 40 знаков, пароль не короче 6" });
      const id = loginId(b.login); users[id] = makeUser(b.login, b.name, "admin", String(b.password)); writeJson(USERS_F, users);
      const t = newSession(id);
      return send(res, 200, { me: { id, login: users[id].login, name: users[id].name, dept: "admin" } }, { "Set-Cookie": cookieHeader(req, t, 2592000) });
    }
    if (p === "/api/login" && req.method === "POST") {
      if (tooMany(ip)) return send(res, 429, { error: "Слишком много попыток, подождите минуту" });
      const b = await readBody(req, 10000);
      const id = loginId(b.login || ""), u = users[id];
      const ok = u && u.dept === b.dept && String(b.password || "").length > 0 &&
        crypto.timingSafeEqual(Buffer.from(hashPw(String(b.password), u.salt), "hex"), Buffer.from(u.hash, "hex"));
      if (!ok) return send(res, 401, { error: "Неверный логин, пароль или департамент" });
      const t = newSession(id);
      return send(res, 200, { me: { id, login: u.login, name: u.name, dept: u.dept } }, { "Set-Cookie": cookieHeader(req, t, b.remember ? 2592000 : 0 || 43200) });
    }
    if (p === "/api/logout" && req.method === "POST") {
      const t = parseCookies(req).evac_sid; if (t) sessions.delete(t);
      return send(res, 200, { ok: true }, { "Set-Cookie": cookieHeader(req, "", 0) });
    }
    if (!me) return send(res, 401, { error: "Нужно войти" });

    if (p === "/api/app" && req.method === "GET") return send(res, 200, { docs: appDocs });
    if (p === "/api/users" && req.method === "GET") return send(res, 200, { users: publicUsers(me.dept === "admin") });
    if (p === "/api/perms" && req.method === "GET") return send(res, 200, { map: perms ? perms.map : null });
    if (p === "/api/log" && req.method === "GET") return send(res, 200, { entries: logs.slice(0, me.dept === "admin" ? 500 : 30) });
    if (p === "/api/password" && req.method === "POST") {
      if (tooMany("pw|" + me.id)) return send(res, 429, { error: "Слишком много попыток, подождите минуту" });
      const b = await readBody(req, 2000), u = users[me.id];
      if (!b.old || !b.new || String(b.new).length < 6) return send(res, 400, { error: "Новый пароль не короче 6 знаков" });
      if (!crypto.timingSafeEqual(Buffer.from(hashPw(String(b.old), u.salt), "hex"), Buffer.from(u.hash, "hex"))) return send(res, 403, { error: "Старый пароль неверный" });
      const salt = crypto.randomBytes(16).toString("hex");
      u.salt = salt; u.iter = ITER; u.hash = hashPw(String(b.new), salt); writeJson(USERS_F, users);
      const keep = parseCookies(req).evac_sid;
      for (const [t, uid] of sessions) if (uid === me.id && t !== keep) sessions.delete(t);
      return send(res, 200, { ok: true });
    }
    if (p === "/api/ext" && req.method === "GET") return send(res, 200, publicExt(me));
    if (p === "/api/status" && req.method === "POST") {
      const b = await readBody(req, 2000);
      const dept = (me.dept === "admin" && b.dept) ? String(b.dept) : me.dept, kind = String(b.kind || "");
      if (!STATUS_KINDS[dept] || !STATUS_KINDS[dept].includes(kind)) return send(res, 403, { error: "Нет такого статуса для вашего департамента" });
      if (me.dept !== "admin" && me.dept !== dept) return send(res, 403, { error: "Нет прав" });
      ext.status[dept] = ext.status[dept] || {};
      if (b.ready) {
        ext.status[dept][kind] = { ready: true, t: Date.now(), by: me.name, dirty: false };
        addLogText(me, "Подтвердил(а): " + KIND_LABEL[kind] + " готов");
        if (mailCfg.evReady) mailAdmins("Готово: " + DEPT_LABEL[dept] + " — " + KIND_LABEL[kind], DEPT_LABEL[dept] + ": " + KIND_LABEL[kind] + " подтверждён (" + me.name + ").");
        if (mailCfg.evAll && allReady()) mailAdmins("Все департаменты подтвердили данные", "Все департаменты подтвердили план, факт и остальные данные. Месяц можно закрывать.");
      } else {
        delete ext.status[dept][kind];
        addLogText(me, "Снял(а) подтверждение: " + KIND_LABEL[kind]);
      }
      saveExt(); return send(res, 200, { ok: true });
    }
    if (p === "/api/comments" && req.method === "POST") {
      if (me.dept !== "manager" && me.dept !== "admin") return send(res, 403, { error: "Комментировать могут руководитель и администратор" });
      const b = await readBody(req, 5000); const text = String(b.text || "").trim().slice(0, 1000);
      if (!text) return send(res, 400, { error: "Пустой комментарий" });
      ext.comments.unshift({ id: crypto.randomBytes(6).toString("hex"), t: Date.now(), u: me.id, n: me.name, text, loc: String(b.loc || "").slice(0, 40) });
      ext.comments = ext.comments.slice(0, 200); saveExt(); return send(res, 200, { ok: true });
    }
    let mc;
    if ((mc = p.match(/^\/api\/comments\/([0-9a-f]{12})$/)) && req.method === "DELETE") {
      const c = ext.comments.find(x => x.id === mc[1]); if (!c) return send(res, 404, { error: "Не найдено" });
      if (me.dept !== "admin" && c.u !== me.id) return send(res, 403, { error: "Удалить можно только свой комментарий" });
      ext.comments = ext.comments.filter(x => x.id !== mc[1]); saveExt(); return send(res, 200, { ok: true });
    }
    if (p === "/api/events" && req.method === "GET") {
      res.writeHead(200, { "Content-Type": "text/event-stream", "Cache-Control": "no-store", "Connection": "keep-alive", "X-Accel-Buffering": "no" });
      res.write("retry: 3000\n\n");
      const c = { res, uid: me.id }; clients.add(c);
      const ping = setInterval(() => { try { res.write(": ping\n\n"); } catch (e) {} }, 25000);
      req.on("close", () => { clearInterval(ping); clients.delete(c); });
      return;
    }
    let m;
    if ((m = p.match(/^\/api\/app\/([A-Za-z0-9_]{1,40})$/))) {
      const id = m[1];
      if (req.method === "PUT") {
        const den = writeDenied(me, id); if (den) return send(res, 403, { error: den });
        const b = await readBody(req, 2 * 1024 * 1024);
        if (!b || typeof b !== "object" || Array.isArray(b)) return send(res, 400, { error: "Неверные данные" });
        const before = appDocs[id], oldCursor = id === "meta" && before ? before.monthCursor : undefined;
        const changed = JSON.stringify(before) !== JSON.stringify(b);
        appDocs[id] = b; writeJson(path.join(APP_DIR, id + ".json"), b);
        if (changed) { try { recordHistory(me, id, before, b); } catch (e) { console.error("history:", e.message); } }
        broadcast("app", { id, data: b }); addLog(me, id);
        if (changed && me.dept !== "admin") {
          const ak = AREA_KIND[id];
          if (ak) {
            let kinds = [ak.kind];
            if (id === "routes") {
              const fa = flatten(before || {}, "", {}), fb = flatten(b, "", {}); kinds = [];
              for (const k of new Set(Object.keys(fa).concat(Object.keys(fb)))) if (fa[k] !== fb[k]) kinds.push(/\.fact$/.test(k) ? "railfact" : "rail");
              kinds = [...new Set(kinds)];
            }
            let mark = false;
            for (const kd of kinds) { const st = ext.status[ak.dept] && ext.status[ak.dept][kd]; if (st && st.ready && !st.dirty) { st.dirty = true; mark = true; } }
            if (mark) saveExt();
          }
        }
        if (id === "meta" && oldCursor !== undefined && b.monthCursor !== oldCursor) {
          ext.status = {}; ext.deadlines = {}; ext.reminded = {}; saveExt();
          if (mailCfg.evClosed) mailAll("Месяц закрыт", "Администратор закрыл месяц и открыл новый. Данные для заполнения обнулены. Сроки нужно задать заново.");
        }
        return send(res, 200, { ok: true });
      }
      if (req.method === "DELETE") {
        { const den2 = writeDenied(me, id); if (den2) return send(res, 403, { error: den2 }); }
        delete appDocs[id]; try { fs.unlinkSync(path.join(APP_DIR, id + ".json")); } catch (e) {}
        broadcast("app", { id, data: null }); return send(res, 200, { ok: true });
      }
    }
    // ---- только администратор ----
    if (me.dept !== "admin") return send(res, 403, { error: "Только администратор" });
    if (p === "/api/users" && req.method === "POST") {
      const b = await readBody(req, 10000);
      if (!b.login || String(b.login).length > 40) return send(res, 400, { error: "Логин до 40 знаков" });
      if (!b.password || String(b.password).length < 6) return send(res, 400, { error: "Пароль короче 6 знаков" });
      if (!ALL_DEPTS.includes(b.dept)) return send(res, 400, { error: "Неизвестный департамент" });
      const id = loginId(b.login); if (users[id]) return send(res, 409, { error: "Такой логин уже есть" });
      users[id] = makeUser(b.login, b.name, b.dept, String(b.password));
      if (b.email) { const em = String(b.email).trim(); if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(em)) return send(res, 400, { error: "Неверный e-mail" }); users[id].email = em; }
      writeJson(USERS_F, users);
      broadcast("users", {}); return send(res, 200, { ok: true });
    }
    if ((m = p.match(/^\/api\/users\/(u_[0-9a-f]+)$/))) {
      const id = m[1]; if (!users[id]) return send(res, 404, { error: "Нет такого пользователя" });
      if (req.method === "DELETE") {
        if (id === me.id) return send(res, 400, { error: "Себя удалить нельзя" });
        delete users[id]; writeJson(USERS_F, users);
        for (const [t, uid] of sessions) if (uid === id) sessions.delete(t);
        broadcast("users", {}); return send(res, 200, { ok: true });
      }
      if (req.method === "PUT") {
        const b = await readBody(req, 10000), u = users[id];
        if (b.email !== undefined) {
          const em = String(b.email || "").trim();
          if (em && !/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(em)) return send(res, 400, { error: "Неверный e-mail" });
          if (em) u.email = em; else delete u.email;
        }
        if (b.password !== undefined) {
          if (String(b.password).length < 6) return send(res, 400, { error: "Пароль короче 6 знаков" });
          const salt = crypto.randomBytes(16).toString("hex");
          u.salt = salt; u.iter = ITER; u.hash = hashPw(String(b.password), salt);
          if (id !== me.id) for (const [t, uid] of sessions) if (uid === id) sessions.delete(t);
        }
        writeJson(USERS_F, users); broadcast("users", {});
        return send(res, 200, { ok: true });
      }
    }
    if (p === "/api/perms" && req.method === "PUT") {
      const b = await readBody(req, 20000);
      if (!b.map || typeof b.map !== "object") return send(res, 400, { error: "Неверные данные" });
      perms = { map: b.map }; writeJson(PERMS_F, perms); broadcast("perms", {}); return send(res, 200, { ok: true });
    }
    if (p === "/api/deadlines" && req.method === "PUT") {
      const b = await readBody(req, 2000), d = {};
      for (const k of ["plan", "fact", "import", "rail"]) { const v = String(b[k] || ""); if (v && !/^\d{4}-\d{2}-\d{2}$/.test(v)) return send(res, 400, { error: "Неверная дата" }); if (v) d[k] = v; }
      ext.deadlines = d; saveExt(); return send(res, 200, { ok: true });
    }
    if (p === "/api/history" && req.method === "GET") return send(res, 200, { rows: history.slice(-4000).reverse() });
    if (p === "/api/mail" && req.method === "GET") { const c = Object.assign({}, mailCfg); c.hasPass = !!c.pass; delete c.pass; return send(res, 200, { cfg: c, log: mailLog }); }
    if (p === "/api/mail" && req.method === "PUT") {
      const b = await readBody(req, 5000), n = Object.assign({}, mailCfg);
      for (const k of ["host", "user", "from", "siteUrl"]) if (b[k] !== undefined) n[k] = String(b[k]).trim().slice(0, 200);
      if (b.pass) n.pass = String(b.pass).slice(0, 200);
      if (b.port !== undefined) n.port = parseInt(b.port, 10) || 0;
      if (["ssl", "starttls", "plain"].includes(b.mode)) n.mode = b.mode;
      for (const k of ["enabled", "evReady", "evAll", "evClosed", "evRemind"]) if (b[k] !== undefined) n[k] = !!b[k];
      mailCfg = n; writeJson(MAIL_F, mailCfg); return send(res, 200, { ok: true });
    }
    if (p === "/api/mail/test" && req.method === "POST") {
      const b = await readBody(req, 2000), to = String(b.to || "").trim();
      if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(to)) return send(res, 400, { error: "Укажите e-mail для проверки" });
      if (!mailCfg.host) return send(res, 400, { error: "Сначала заполните адрес почтового сервера" });
      try { await smtpSend(mailCfg, [to], "[Эвакуация КТК] Проверка почты", "Это тестовое письмо. Если вы его видите, почта настроена верно."); return send(res, 200, { ok: true }); }
      catch (e) { mailLog.unshift({ t: Date.now(), to: to, s: "Проверка почты", ok: false, err: mailErrText(e) }); return send(res, 400, { error: mailErrText(e) }); }
    }
    if (p === "/api/backups" && req.method === "GET") return send(res, 200, { list: backupList() });
    if (p === "/api/backups" && req.method === "POST") { try { return send(res, 200, { name: makeBackup("hand" + new Date().toISOString().slice(11, 19).replace(/:/g, "")) }); } catch (e) { return send(res, 400, { error: e.message }); } }
    let mb;
    if ((mb = p.match(/^\/api\/backups\/(evac-[0-9a-z-]{4,40}\.json)$/)) && req.method === "GET") {
      const f = path.join(BK_DIR, mb[1]); if (!fs.existsSync(f)) return send(res, 404, { error: "Нет такой копии" });
      const data = fs.readFileSync(f);
      res.writeHead(200, { "Content-Type": "application/json", "Content-Disposition": 'attachment; filename="' + mb[1] + '"', "Content-Length": data.length, "Cache-Control": "no-store" });
      return res.end(data);
    }
    if ((mb = p.match(/^\/api\/backups\/(evac-[0-9a-z-]{4,40}\.json)\/restore$/)) && req.method === "POST") {
      if (!fs.existsSync(path.join(BK_DIR, mb[1]))) return send(res, 404, { error: "Нет такой копии" });
      try { restoreBackup(mb[1]); addLogText(me, "Восстановил(а) данные из копии " + mb[1]); return send(res, 200, { ok: true }); } catch (e) { return send(res, 400, { error: e.message }); }
    }
    return send(res, 404, { error: "Не найдено" });
  } catch (e) {
    return send(res, 400, { error: e.message || "Ошибка запроса" });
  }
});
setInterval(() => { dailyBackup(); remindersCheck(); }, 10 * 60 * 1000);
setTimeout(() => { dailyBackup(); remindersCheck(); }, 5000);
server.listen(PORT, () => console.log("Эвакуация КТК: http://localhost:" + PORT + "  (данные: " + DATA_DIR + ")"));
