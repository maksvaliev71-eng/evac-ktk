// Сервер «Эвакуация КТК». Без внешних зависимостей, нужен Node.js 18 или новее.
// Запуск: node server.js   (порт и папка данных задаются переменными PORT и DATA_DIR)
"use strict";
const http = require("http"), fs = require("fs"), path = require("path"), crypto = require("crypto");

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
const ALL_DEPTS = DEPT_KEYS.concat(["viewer", "admin"]);

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
  return permsFor(me.dept).includes(a);
}

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

// ---------- HTTP ----------
function send(res, code, obj, headers) {
  const body = typeof obj === "string" ? obj : JSON.stringify(obj);
  res.writeHead(code, Object.assign({ "Content-Type": typeof obj === "string" ? "text/html; charset=utf-8" : "application/json; charset=utf-8", "Cache-Control": "no-store", "X-Content-Type-Options": "nosniff" }, headers || {}));
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
function publicUsers() {
  const o = {}; for (const id of Object.keys(users)) o[id] = { login: users[id].login, name: users[id].name, dept: users[id].dept }; return o;
}
function cookieHeader(req, token, maxAge) {
  const secure = (req.headers["x-forwarded-proto"] === "https") ? "; Secure" : "";
  return "evac_sid=" + token + "; HttpOnly; SameSite=Lax; Path=/; Max-Age=" + maxAge + secure;
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, "http://x"); const p = url.pathname;
  try {
    if (req.method === "GET" && (p === "/" || p === "/index.html")) {
      return send(res, 200, fs.readFileSync(INDEX, "utf8"));
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
    if (p === "/api/users" && req.method === "GET") return send(res, 200, { users: publicUsers() });
    if (p === "/api/perms" && req.method === "GET") return send(res, 200, { map: perms ? perms.map : null });
    if (p === "/api/log" && req.method === "GET") {
      if (me.dept !== "admin") return send(res, 403, { error: "Только администратор" });
      return send(res, 200, { entries: logs.slice(0, 80) });
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
        if (!canWriteDoc(me, id)) return send(res, 403, { error: "Нет прав на изменение этой части данных" });
        const b = await readBody(req, 2 * 1024 * 1024);
        if (!b || typeof b !== "object" || Array.isArray(b)) return send(res, 400, { error: "Неверные данные" });
        appDocs[id] = b; writeJson(path.join(APP_DIR, id + ".json"), b);
        broadcast("app", { id, data: b }); addLog(me, id);
        return send(res, 200, { ok: true });
      }
      if (req.method === "DELETE") {
        if (!canWriteDoc(me, id)) return send(res, 403, { error: "Нет прав" });
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
      users[id] = makeUser(b.login, b.name, b.dept, String(b.password)); writeJson(USERS_F, users);
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
        const b = await readBody(req, 10000);
        if (!b.password || String(b.password).length < 6) return send(res, 400, { error: "Пароль короче 6 знаков" });
        const u = users[id], salt = crypto.randomBytes(16).toString("hex");
        u.salt = salt; u.iter = ITER; u.hash = hashPw(String(b.password), salt); writeJson(USERS_F, users);
        if (id !== me.id) for (const [t, uid] of sessions) if (uid === id) sessions.delete(t);
        return send(res, 200, { ok: true });
      }
    }
    if (p === "/api/perms" && req.method === "PUT") {
      const b = await readBody(req, 20000);
      if (!b.map || typeof b.map !== "object") return send(res, 400, { error: "Неверные данные" });
      perms = { map: b.map }; writeJson(PERMS_F, perms); broadcast("perms", {}); return send(res, 200, { ok: true });
    }
    return send(res, 404, { error: "Не найдено" });
  } catch (e) {
    return send(res, 400, { error: e.message || "Ошибка запроса" });
  }
});
server.listen(PORT, () => console.log("Эвакуация КТК: http://localhost:" + PORT + "  (данные: " + DATA_DIR + ")"));
