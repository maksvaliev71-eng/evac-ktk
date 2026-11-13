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
  rail: ["routes", "trainsCfg"],
  expl: ["fact_expl", "import_fact", "stock"],
};
// частичные права: что можно менять внутри общего документа
const IMPFW = []; for (let i = 0; i < 5; i++) { IMPFW.push("impFw" + i + "_20", "impFw" + i + "_40"); }
const PARTIAL = { import: { need: "import_fact", fields: ["impF20", "impF40"].concat(IMPFW) }, inputs: { need: "stock", fields: ["resource20", "resource40", "stockNow20", "stockNow40", "stockNowTs"] } };
const DEPT_KEYS = ["vnutriros", "export", "import", "rail", "expl"];
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
const MAIL_DEF = { evPlans: true, enabled: false, mode: "ssl", host: "", port: 465, user: "", pass: "", from: "", siteUrl: "", evReady: true, evAll: true, evClosed: true, evRemind: true, evWeekly: true, evCloseRpt: true, weeklyDay: 1 };
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
  const P = permsFor(me.dept);
  return P.includes(a) || !!(PARTIAL[a] && P.includes(PARTIAL[a].need));
}
// поля, которые можно менять (null — документ можно менять целиком)
function partialFields(me, id) {
  if (me.dept === "admin") return null;
  const a = areaOfDoc(id), P = permsFor(me.dept);
  return (PARTIAL[a] && !P.includes(a) && P.includes(PARTIAL[a].need)) ? PARTIAL[a].fields : null;
}
// какой части статуса соответствует область данных
const AREA_KIND = {
  plan_vnutriros: { dept: "vnutriros", kind: "plan" }, fact_vnutriros: { dept: "vnutriros", kind: "fact" },
  plan_export: { dept: "export", kind: "plan" }, fact_export: { dept: "export", kind: "fact" },
  import: { dept: "import", kind: "import" }, routes: { dept: "rail", kind: "rail" },
  plan_expl: { dept: "expl", kind: "plan" }, fact_expl: { dept: "expl", kind: "fact" },
};
const STATUS_KINDS = { vnutriros: ["plan", "fact"], export: ["plan", "fact"], expl: ["plan", "fact"], import: ["import"], rail: ["rail", "railfact"] };
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
  if (me.dept !== "admin" && areaOfDoc(id) === "routes") {
    // поезда: срок проверяется по изменённым полям (см. обработчик PUT); целиком документ закрыт, только если закрыты оба срока
    if (deadlineLocked("rail") && deadlineLocked("fact")) return "Срок внесения истёк (" + fmtDate(ext.deadlines.rail || ext.deadlines.fact) + "). Обратитесь к администратору";
  } else if (me.dept !== "admin") {
    const ak = AREA_KIND[areaOfDoc(id)];
    // отдел без права на весь раздел «Импорт» (Эксплуатация вносит только факт) подчиняется сроку «факт», а не сроку отдела «Импорт»
    const kind = ak ? ((areaOfDoc(id) === "import" && !permsFor(me.dept).includes("import")) ? "fact" : ak.kind) : null;
    if (kind && deadlineLocked(kind)) return "Срок внесения истёк (" + fmtDate(ext.deadlines[kind]) + "). Обратитесь к администратору";
  }
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
// кто сейчас вводит какую ячейку
const presence = new Map();
let presenceSig = "";
function presenceList() { return [...presence].map(([uid, v]) => ({ uid, key: v.key, name: v.name })); }
function presenceBroadcast() { const l = presenceList(), sig = JSON.stringify(l); if (sig === presenceSig) return; presenceSig = sig; broadcast("presence", l); }
setInterval(() => { const now = Date.now(); let ch = false; for (const [u, v] of presence) if (now - v.t > 20000) { presence.delete(u); ch = true; } if (ch) presenceBroadcast(); }, 5000);
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
function smtpSend(cfg, rcpts, subject, text, html) {
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
        "Message-ID: <" + crypto.randomBytes(8).toString("hex") + "@evac.local>", "MIME-Version: 1.0"].concat(html ? ["Content-Type: multipart/alternative; boundary=\"evacB\""] : ["Content-Type: text/plain; charset=utf-8", "Content-Transfer-Encoding: base64"]).join("\r\n");
      const wrap = t => b64(t).replace(/.{1,76}/g, "$&\r\n");
      const body = html
        ? "--evacB\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Transfer-Encoding: base64\r\n\r\n" + wrap(text) + "--evacB\r\nContent-Type: text/html; charset=utf-8\r\nContent-Transfer-Encoding: base64\r\n\r\n" + wrap(html) + "--evacB--\r\n"
        : wrap(text);
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
function sendMail(rcpts, subject, text, html) {
  { const seen = new Set(); rcpts = rcpts.filter(Boolean).filter(a => { const k = addrOnly(a).toLowerCase(); if (seen.has(k)) return false; seen.add(k); return true; }); }
  if (!mailCfg.enabled || !mailCfg.host || !rcpts.length) return mailChain;
  const full = (mailCfg.siteUrl ? text + "\n\n" + mailCfg.siteUrl : text);
  const fullHtml = html ? (mailCfg.siteUrl ? html + '<p style="font:13px Arial;color:#667"><a href="' + escH(mailCfg.siteUrl) + '">' + escH(mailCfg.siteUrl) + "</a></p>" : html) : null;
  mailChain = mailChain.then(() => smtpSend(mailCfg, rcpts, "[Эвакуация КТК] " + subject, full, fullHtml)
    .then(() => { mailLog.unshift({ t: Date.now(), to: rcpts.join(", "), s: subject, ok: true }); })
    .catch(e => { mailLog.unshift({ t: Date.now(), to: rcpts.join(", "), s: subject, ok: false, err: mailErrText(e) }); }))
    .then(() => { mailLog.length = Math.min(mailLog.length, 30); });
  return mailChain;
}
function emailsOf(pred) { return Object.values(users).filter(u => u.email && pred(u)).map(u => u.email); }
// подписки на письма: у каждого человека своя настройка, пустое значение — по роли
const SUB_KEYS = ["ready", "all", "closed", "remind", "weekly", "closeRpt", "plans"];
function defSub(u, k) {
  switch (k) {
    case "ready": case "all": return u.dept === "admin";
    case "closed": case "plans": return true;
    case "remind": return u.dept !== "manager" && u.dept !== "viewer";
    case "weekly": return u.dept === "admin" || !!u.head;
    case "closeRpt": return u.dept === "admin" || u.dept === "manager" || u.dept === "viewer";
  }
  return false;
}
const subOn = (u, k) => (u.subs && u.subs[k] !== undefined ? !!u.subs[k] : defSub(u, k));
const rcptsFor = (k, pred) => emailsOf(u => subOn(u, k) && (!pred || pred(u)));
const mailTo = (k, subj, text) => sendMail(rcptsFor(k), subj, text);

// ---------- отчёты по почте ----------
function escH(v) { return String(v == null ? "" : v).replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c])); }
const nf = n => Math.round(Number(n) || 0).toLocaleString("ru-RU").replace(/\u00a0/g, " ");
const pc = (f, p) => (p > 0 ? Math.round((f / p) * 100) + "%" : "—");
const DIR_NAMES = { vnutriros: "Внутрироссийский", export: "Экспортный", expl: "Эксплуатация" };
const TH = "padding:6px 10px;background:#E8EEF3;text-align:left;font-weight:bold;border:1px solid #D5DDE5", TD = "padding:6px 10px;border:1px solid #D5DDE5";
function tbl(head, rows) {
  return '<table style="border-collapse:collapse;font:13px Arial;margin:6px 0 16px"><tr>' + head.map((h, i) => '<th style="' + TH + (i ? ";text-align:right" : "") + '">' + escH(h) + "</th>").join("") + "</tr>" +
    rows.map(r => "<tr>" + r.map((c, i) => '<td style="' + TD + (i ? ";text-align:right" : "") + '">' + escH(c) + "</td>").join("") + "</tr>").join("") + "</table>";
}
function wrapHtml(title, inner) { return '<div style="font:14px Arial;color:#1B2A38;max-width:760px"><h2 style="margin:0 0 4px;font:bold 18px Arial;color:#004D77">' + escH(title) + "</h2>" + inner + "</div>"; }
function h3(t) { return '<h3 style="font:bold 14px Arial;margin:14px 0 2px">' + escH(t) + "</h3>"; }
function summaryParts(label, totalVolume, totalPlan, totalFact, planByDir, factByDir, railP, railF) {
  let txt = label + "\nОбъём к эвакуации: " + nf(totalVolume) + "\nПлан: " + nf(totalPlan) + "\nФакт: " + nf(totalFact) + " (" + pc(totalFact, totalPlan) + ")\n";
  const rows = Object.keys(DIR_NAMES).map(k => { txt += DIR_NAMES[k] + ": план " + nf((planByDir || {})[k]) + ", факт " + nf((factByDir || {})[k]) + " (" + pc((factByDir || {})[k], (planByDir || {})[k]) + ")\n"; return [DIR_NAMES[k], nf((planByDir || {})[k]), nf((factByDir || {})[k]), pc((factByDir || {})[k], (planByDir || {})[k])]; });
  rows.push(["Всего", nf(totalPlan), nf(totalFact), pc(totalFact, totalPlan)]);
  let html = tbl(["Объём к эвакуации, шт", "План, шт", "Факт, шт", "Выполнение"], [[nf(totalVolume), nf(totalPlan), nf(totalFact), pc(totalFact, totalPlan)]]) + h3("По департаментам") + tbl(["Департамент", "План, шт", "Факт, шт", "Выполнение"], rows);
  if (railP || railF) { html += h3("Поезда") + tbl(["", "План, шт", "Факт, шт", "Выполнение"], [["Поезда", nf(railP), nf(railF), pc(railF, railP)]]); txt += "Поезда: план " + nf(railP) + ", факт " + nf(railF) + "\n"; }
  return { txt, html };
}
function weeklyReport() {
  const sn = ext.snap; if (!sn) return null;
  const sp = summaryParts(sn.label, sn.totalVolume, sn.totalPlan, sn.totalFact, sn.planByDir, sn.factByDir, sn.rail && sn.rail.plan, sn.rail && sn.rail.fact);
  let html = '<p style="margin:0 0 8px;color:#556">Данные на ' + escH(new Date(sn.t + 10 * 3600000).toISOString().slice(0, 16).replace("T", " ")) + " (владивостокское время)</p>" + sp.html, txt = "Недельный отчёт — " + sp.txt;
  const locs = (sn.locs || []).filter(l => l.p > 0).map(l => Object.assign({ gap: l.p - l.f }, l)).sort((a, b) => b.gap - a.gap).slice(0, 10);
  if (locs.length) { html += h3("Локации с наибольшим отставанием от плана") + tbl(["Локация", "План, шт", "Факт, шт", "Выполнение", "Не довезено, шт"], locs.map(l => [l.n, nf(l.p), nf(l.f), pc(l.f, l.p), nf(Math.max(0, l.gap))])); }
  const rows = []; let notReady = 0;
  for (const d of Object.keys(STATUS_KINDS)) for (const k of STATUS_KINDS[d]) {
    const st = ext.status[d] && ext.status[d][k], ok = st && st.ready && !st.dirty; if (!ok) notReady++;
    const dl = ext.deadlines[k === "railfact" ? "fact" : k];
    rows.push([DEPT_LABEL[d] + " — " + KIND_LABEL[k], ok ? "готово" : (st && st.ready ? "изменено после подтверждения" : "ждём"), dl ? fmtDate(dl) : "—"]);
  }
  html += h3("Готовность данных (не подтверждено: " + notReady + ")") + tbl(["Что", "Статус", "Срок"], rows).replace(/text-align:right/g, "text-align:left");
  txt += "Не подтверждено разделов: " + notReady + "\n";
  return { subject: "Недельный отчёт — " + sn.label, text: txt, html: wrapHtml("Недельный отчёт: " + sn.label, html) };
}
function closeReport() {
  const ids = Object.keys(appDocs).filter(k => /^a\d{3}$/.test(k)).sort(); if (!ids.length) return null;
  const a = appDocs[ids[ids.length - 1]], names = (ext.snap && ext.snap.names) || {};
  let rp = 0, rf = 0;
  if (a.routes) Object.values(a.routes).forEach(r => { rp += (r && r.plan) || 0; rf += (r && r.fact) || 0; }); else { rp = a.routesPlan || 0; rf = a.routesFact || 0; }
  const label = (a.label || "") + " " + (a.year || "");
  const sp = summaryParts(label.trim(), a.totalVolume, a.totalPlan, a.totalFact, a.planByDir, a.factByDir, rp, rf);
  let html = sp.html, txt = "Отчёт по закрытию месяца — " + sp.txt;
  const rs = [];
  Object.keys(a.reasons || {}).forEach(d => Object.keys(a.reasons[d] || {}).forEach(l => { const t = a.reasons[d][l]; if (t) rs.push([DIR_NAMES[d] || d, names[l] || l, t]); }));
  if (rs.length) { html += h3("Причины невыполнения плана") + tbl(["Департамент", "Локация", "Причина"], rs).replace(/text-align:right/g, "text-align:left"); txt += "\nПричины невыполнения:\n" + rs.map(r => "- " + r.join(" / ")).join("\n") + "\n"; }
  return { subject: "Месяц закрыт — отчёт: " + label.trim(), text: txt, html: wrapHtml("Отчёт по закрытию месяца: " + label.trim(), html) };
}
function plansAllReady() { return ["vnutriros", "export", "expl"].every(d => { const st = ext.status[d] && ext.status[d].plan; return st && st.ready && !st.dirty; }); }
function plansReport() {
  const sn = ext.snap; if (!sn || !sn.plans || !Object.keys(sn.plans).length) return null;
  const keys = Object.keys(DIR_NAMES), tot = { all: { c20: 0, c40: 0 } };
  keys.forEach(k => { tot[k] = { c20: 0, c40: 0 }; });
  const names = sn.names || {};
  const rows = Object.keys(sn.plans).map(id => {
    const p = sn.plans[id]; let a20 = 0, a40 = 0; const r = [names[id] || id];
    keys.forEach(k => { const q = p[k] || { c20: 0, c40: 0 }; r.push(nf(q.c20), nf(q.c40)); a20 += q.c20; a40 += q.c40; tot[k].c20 += q.c20; tot[k].c40 += q.c40; });
    r.push(nf(a20), nf(a40), nf(a20 + a40)); tot.all.c20 += a20; tot.all.c40 += a40; return r;
  });
  const trow = ["Итого"]; keys.forEach(k => trow.push(nf(tot[k].c20), nf(tot[k].c40))); trow.push(nf(tot.all.c20), nf(tot.all.c40), nf(tot.all.c20 + tot.all.c40)); rows.push(trow);
  const head = ["Локация"]; keys.forEach(k => { head.push(DIR_NAMES[k] + " 20'", DIR_NAMES[k] + " 40'"); }); head.push("Всего 20'", "Всего 40'", "Всего");
  let txt = "Все департаменты подтвердили планы — " + sn.label + "\n\n" + head.join(" | ") + "\n" + rows.map(r => r.join(" | ")).join("\n") + "\n";
  const html = '<p style="margin:0 0 8px;color:#556">Все департаменты нажали «Готово» по планам. Итоговый план по локациям, шт.</p>' + tbl(head, rows);
  return { subject: "Планы подтверждены — " + sn.label, text: txt, html: wrapHtml("Планы всех департаментов: " + sn.label, html) };
}
const reportRcpts = () => rcptsFor("closeRpt");
const weeklyRcpts = () => rcptsFor("weekly");
const plansRcpts = () => rcptsFor("plans");
function sendReport(r, rcpts) { if (r) return sendMail(rcpts || reportRcpts(), r.subject, r.text, r.html); return Promise.resolve(); }
function weeklyCheck() {
  if (!mailCfg.enabled || !mailCfg.evWeekly) return;
  const msk = new Date(Date.now() + 3 * 3600000), today = mskToday();
  if ((msk.getUTCDay() || 7) !== (parseInt(mailCfg.weeklyDay, 10) || 1) || msk.getUTCHours() < 9 || ext.lastWeekly === today) return;
  const r = weeklyReport(); if (!r) return;
  ext.lastWeekly = today; writeJson(EXT_F, ext); sendReport(r, weeklyRcpts());
}


// ---------- хранение контейнеров на терминалах (только админ и Эксплуатация) ----------
const ST_DIR = path.join(DATA_DIR, "storage"); fs.mkdirSync(ST_DIR, { recursive: true });
const ST_CFG_F = path.join(ST_DIR, "config.json"), ST_IDX_F = path.join(ST_DIR, "index.json");
const ST_BASE = "2000-01"; // «с начала»: первая версия тарифа действует и на более ранние месяцы
let stIdx = readJson(ST_IDX_F, {});
const stOk = me => !!me && (me.dept === "admin" || me.dept === "expl");
const stYmOk = s => /^\d{4}-(0[1-9]|1[0-2])$/.test(String(s || ""));
const stMF = ym => path.join(ST_DIR, "m-" + ym + ".json");
function stWrite(f, obj) { try { if (fs.existsSync(f)) fs.copyFileSync(f, f + ".bak"); } catch (e) {} writeJson(f, obj); }
function stNum(v, max) { const n = Number(String(v === undefined || v === null ? "" : v).replace(",", ".").replace(/\s/g, "")); return isFinite(n) && n >= 0 ? Math.min(Math.round(n * 100) / 100, max || 1e9) : 0; }
function stTariff(t) { t = t || {}; return { prr: stNum(t.prr), rate: stNum(t.rate), free: Math.round(stNum(t.free, 3650)) }; }
// версии тарифов терминала: [{from:"YYYY-MM", t20, t40}], по возрастанию from; первая действует и на более ранние месяцы
function stVersions(vs) {
  const m = new Map();
  for (const v of vs || []) { const f = String((v && v.from) || ""); if (stYmOk(f)) m.set(f, { from: f, t20: stTariff(v.t20), t40: stTariff(v.t40) }); }
  const arr = [...m.values()].sort((a, b) => a.from.localeCompare(b.from));
  return arr.length ? arr : [{ from: ST_BASE, t20: stTariff(), t40: stTariff() }];
}
function stCleanTerm(t, id) {
  const vs = Array.isArray(t.tariffs) ? t.tariffs : ((t.t20 || t.t40) ? [{ from: ST_BASE, t20: t.t20, t40: t.t40 }] : []);
  return { id, city: String(t.city || "").trim().slice(0, 60) || "Без города", name: String(t.name || "").trim().slice(0, 80), tariffs: stVersions(vs), archived: !!t.archived };
}
let stCfg = readJson(ST_CFG_F, { terminals: [] }); if (!Array.isArray(stCfg.terminals)) stCfg.terminals = [];
stCfg.terminals = stCfg.terminals.map(t => stCleanTerm(t, t.id));
// ставки терминала на месяц: последняя версия с from <= месяца, иначе первая
function stRates(term, ym) { let r = term.tariffs[0]; for (const v of term.tariffs) if (v.from <= ym) r = v; return r; }
function stDay(s) {
  const m = /^(\d{4})-(\d{2})-(\d{2})$/.exec(String(s || "")); if (!m) return null;
  const t = Date.UTC(+m[1], +m[2] - 1, +m[3]); if (new Date(t).getUTCMonth() !== +m[2] - 1) return null; return Math.round(t / 86400000);
}
function stMonthRange(ym) { const y = +ym.slice(0, 4), m = +ym.slice(5, 7); return [Math.round(Date.UTC(y, m - 1, 1) / 86400000), Math.round(Date.UTC(y, m, 0) / 86400000)]; }
const stIso = d => new Date(d * 86400000).toISOString().slice(0, 10);
function stPrevYm(ym) { const y = +ym.slice(0, 4), m = +ym.slice(5, 7); return m === 1 ? (y - 1) + "-12" : y + "-" + String(m - 1).padStart(2, "0"); }
const stR2 = v => Math.round(v * 100) / 100;
// терминал для расчёта месяца: из актуального списка (ставки на месяц tm), а если его там уже нет — из снимка в файле месяца
function stTermFor(mf, id, tm) {
  const c = stCfg.terminals.find(t => t.id === id);
  if (c) { const r = stRates(c, tm); return { name: c.name, city: c.city, from: r.from, t20: r.t20, t40: r.t40 }; }
  const s = (mf.terms || {})[id]; return s ? { name: s.name, city: s.city, from: s.from || "", t20: s.t20, t40: s.t40 } : null;
}
// Расчёт месяца. Каждый месяц считается отдельно, только за свои сутки и свои операции — поэтому
// контейнер, стоящий несколько месяцев, нигде не считается дважды.
// • Сутки заезда и выезда считаются оба; без выезда — по «сегодня» (но не дальше конца месяца).
// • Бесплатные дни — один раз от даты заезда (в т.ч. заезд в прошлом месяце).
// • Крановые операции: 1 за заезд в этом месяце + 1 за выезд в этом месяце (0–2).
function stCalc(mf, today, opts) {
  const tm = (opts && opts.tmonth) || mf.month, [ms, me_] = stMonthRange(mf.month), td = stDay(today), asOf = Math.min(td === null ? me_ : td, me_);
  const tc = {}, out = [], by = {}, terms = {}, tot = { cnt20: 0, cnt40: 0, days: 0, paid: 0, st: 0, ops: 0, prr: 0, tot: 0, open: 0 };
  for (const r of mf.rows || []) {
    const tmx = tc[r.t] !== undefined ? tc[r.t] : (tc[r.t] = stTermFor(mf, r.t, tm)); if (!tmx) continue;
    terms[r.t] = tmx;
    const tf = r.s === 40 ? tmx.t40 : tmx.t20, inD = stDay(r.i), outD = r.o ? stDay(r.o) : null; if (inD === null) continue;
    const start = Math.max(inD, ms), end = Math.min(outD !== null ? outD : asOf, me_), open = outD === null;
    const days = Math.max(0, end - start + 1), paid = Math.max(0, end - Math.max(start, inD + tf.free) + 1);
    const ops = (inD >= ms && inD <= me_ ? 1 : 0) + (outD !== null && outD >= ms && outD <= me_ ? 1 : 0);
    const st = stR2(paid * tf.rate), prr = stR2(ops * tf.prr), row = { t: r.t, c: r.c, s: r.s, i: r.i, o: r.o || "", n: ops, days, free: tf.free, paid, st, prr, tot: stR2(st + prr), open };
    out.push(row);
    const b = by[r.t] || (by[r.t] = { cnt20: 0, cnt40: 0, days: 0, paid: 0, st: 0, ops: 0, prr: 0, tot: 0, open: 0 });
    for (const o of [b, tot]) { if (r.s === 40) o.cnt40++; else o.cnt20++; o.days += days; o.paid += paid; o.st += st; o.ops += ops; o.prr += prr; o.tot += row.tot; if (open) o.open++; }
  }
  for (const o of Object.values(by).concat([tot])) { o.st = stR2(o.st); o.prr = stR2(o.prr); o.tot = stR2(o.tot); }
  return { rows: out, byTerm: by, tot, terms, asOf: stIso(asOf) };
}
function stSnapTerms(ym) { const o = {}; for (const t of stCfg.terminals) { const r = stRates(t, ym); o[t.id] = { name: t.name, city: t.city, from: r.from, t20: r.t20, t40: r.t40 }; } return o; }
function stIndexEntry(mf, res) {
  const tn = {}; for (const id of Object.keys(res.terms)) tn[id] = { n: res.terms[id].name, c: res.terms[id].city };
  return { rows: (mf.rows || []).length, uploadedAt: mf.uploadedAt, by: mf.by, asOf: res.asOf, sum: res.tot, byTerm: res.byTerm, tn };
}
function stList() {
  const today = mskToday(), months = []; let changed = false;
  let files = []; try { files = fs.readdirSync(ST_DIR).filter(f => /^m-\d{4}-\d{2}\.json$/.test(f)); } catch (e) {}
  for (const f of files) {
    const ym = f.slice(2, 9); const [, me_] = stMonthRange(ym), td = stDay(today), want = stIso(Math.min(td, me_));
    let e = stIdx[ym];
    if (!e || e.asOf !== want || !e.byTerm) { const mf = readJson(path.join(ST_DIR, f), null); if (!mf) continue; e = stIdx[ym] = stIndexEntry(mf, stCalc(mf, today)); changed = true; }
    months.push({ month: ym, rows: e.rows, uploadedAt: e.uploadedAt, by: e.by, asOf: e.asOf, sum: e.sum, byTerm: e.byTerm, tn: e.tn });
  }
  if (changed) { try { writeJson(ST_IDX_F, stIdx); } catch (e) {} }
  return months.sort((a, b) => b.month.localeCompare(a.month));
}
function stNorm(s) { return String(s || "").trim().toLowerCase().replace(/\s+/g, " "); }
// контроль между месяцами: контейнеры, стоявшие на терминале в конце прошлого месяца, но отсутствующие в файле этого месяца
function stContinuity(ym, mf) {
  const pym = stPrevYm(ym), pf = readJson(stMF(pym), null); if (!pf) return null;
  const [, pe] = stMonthRange(pym), cur = new Set((mf.rows || []).map(r => r.t + "|" + r.c)), list = [];
  for (const r of pf.rows || []) { const od = r.o ? stDay(r.o) : null; if ((od === null || od > pe) && !cur.has(r.t + "|" + r.c)) { const t = stTermFor(pf, r.t, pym); list.push({ t: t ? t.name : "?", c: r.c, s: r.s, i: r.i }); } }
  return { prev: pym, count: list.length, list: list.slice(0, 100) };
}

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
    const d = ext.deadlines[kind === "railfact" ? "fact" : kind]; if (!d || (d !== today && d !== tomorrow)) continue;
    const st = ext.status[dept] && ext.status[dept][kind]; if (st && st.ready && !st.dirty) continue;
    const key = dept + "|" + kind + "|" + d + "|" + today; if (ext.reminded[key]) continue;
    ext.reminded[key] = 1; dirty = true;
    ((s2, t2) => sendMail(rcptsFor("remind", u => u.dept === dept || (dept === "expl" && kind === "plan" && u.dept === "admin")), s2, t2))("Напоминание: срок — " + KIND_LABEL[kind], "Срок внесения («" + KIND_LABEL[kind] + "») — " + fmtDate(d) + (d === today ? " (сегодня)" : " (завтра)") + ". Данные ещё не подтверждены кнопкой «Готово».");
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
  const o = {}; for (const id of Object.keys(users)) { o[id] = { login: users[id].login, name: users[id].name, dept: users[id].dept }; if (withEmail) { o[id].email = users[id].email || ""; o[id].head = !!users[id].head; o[id].subs = {}; SUB_KEYS.forEach(k => { o[id].subs[k] = subOn(users[id], k); }); } } return o;
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
      if (me.dept === "expl" && kind !== "fact") return send(res, 403, { error: "Эксплуатация подтверждает только факт" });
      ext.status[dept] = ext.status[dept] || {};
      if (b.ready) {
        ext.status[dept][kind] = { ready: true, t: Date.now(), by: me.name, dirty: false };
        addLogText(me, "Подтвердил(а): " + KIND_LABEL[kind] + " готов");
        if (kind === "plan" && plansAllReady() && !ext.plansReported) {
          ext.plansReported = true;
          if (mailCfg.enabled && mailCfg.evPlans) setTimeout(() => { try { sendReport(plansReport(), plansRcpts()); } catch (e) { console.error("plansReport:", e.message); } }, 10000);
        }
        if (mailCfg.evReady) mailTo("ready", "Готово: " + DEPT_LABEL[dept] + " — " + KIND_LABEL[kind], DEPT_LABEL[dept] + ": " + KIND_LABEL[kind] + " подтверждён (" + me.name + ").");
        if (mailCfg.evAll && allReady()) mailTo("all", "Все департаменты подтвердили данные", "Все департаменты подтвердили план, факт и остальные данные. Месяц можно закрывать.");
      } else {
        delete ext.status[dept][kind]; if (kind === "plan") ext.plansReported = false;
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
    if (p.startsWith("/api/storage")) {
      if (!stOk(me)) return send(res, 403, { error: "Раздел доступен только администратору и Эксплуатации" });
      if (p === "/api/storage" && req.method === "GET") return send(res, 200, { cfg: stCfg, months: stList(), today: mskToday() });
      if (p === "/api/storage/analytics" && req.method === "GET") {
        const ms2 = stList().slice().reverse(), terms = {}, rates = {}, fx = {}, today = mskToday();
        for (const m of ms2) for (const id of Object.keys(m.tn || {})) terms[id] = m.tn[id];
        const out = ms2.map(m => {
          const [, me2] = stMonthRange(m.month), mf = readJson(stMF(m.month), null); rates[m.month] = {}; fx[m.month] = {};
          if (mf) {
            const cur = stCalc(mf, today), pym = stPrevYm(m.month), prev = stCalc(mf, today, { tmonth: pym });
            for (const id of Object.keys(cur.terms)) {
              const t = cur.terms[id]; rates[m.month][id] = { from: t.from, t20: t.t20, t40: t.t40 };
              const d = stR2(((cur.byTerm[id] || {}).tot || 0) - ((prev.byTerm[id] || {}).tot || 0)); if (d) fx[m.month][id] = d;
            }
          }
          return { month: m.month, asOf: m.asOf, partial: stDay(m.asOf) < me2, byTerm: m.byTerm, tot: m.sum };
        });
        return send(res, 200, { months: out, terms, rates, fx });
      }
      if (p === "/api/storage/cfg" && req.method === "PUT") {
        const b = await readBody(req, 2000000); if (!Array.isArray(b.terminals) || b.terminals.length > 300) return send(res, 400, { error: "Неверные данные" });
        const used = new Set(), list = [];
        for (const t of b.terminals) {
          const name = String(t.name || "").trim().slice(0, 80); if (!name) continue;
          let id = /^[0-9a-f]{8}$/.test(String(t.id || "")) && !used.has(t.id) ? t.id : ""; while (!id || used.has(id)) id = crypto.randomBytes(4).toString("hex");
          used.add(id); list.push(stCleanTerm(Object.assign({}, t, { name }), id));
        }
        stCfg = { terminals: list }; stWrite(ST_CFG_F, stCfg); stIdx = {}; try { writeJson(ST_IDX_F, stIdx); } catch (e) {} addLogText(me, "Хранение: изменил(а) терминалы и тарифы"); broadcast("storage", {});
        return send(res, 200, { ok: true, cfg: stCfg });
      }
      let sm;
      if ((sm = p.match(/^\/api\/storage\/month\/(\d{4}-\d{2})(\/retariff)?$/)) && stYmOk(sm[1])) {
        const ym = sm[1], f = stMF(ym);
        if (!sm[2] && req.method === "GET") {
          const mf = readJson(f, null); if (!mf) return send(res, 404, { error: "Нет данных за этот месяц" });
          const result = stCalc(mf, mskToday()); stIdx[ym] = stIndexEntry(mf, result);
          return send(res, 200, { month: ym, uploadedAt: mf.uploadedAt, by: mf.by, terms: result.terms, result, continuity: stContinuity(ym, mf) });
        }
        if (!sm[2] && req.method === "DELETE") {
          if (!fs.existsSync(f)) return send(res, 404, { error: "Нет данных" });
          try { fs.copyFileSync(f, f + ".deleted"); fs.unlinkSync(f); } catch (e) {} delete stIdx[ym]; try { writeJson(ST_IDX_F, stIdx); } catch (e) {}
          addLogText(me, "Хранение: удалил(а) данные за " + ym); broadcast("storage", {}); return send(res, 200, { ok: true });
        }
        if (!sm[2] && req.method === "PUT") {
          const b = await readBody(req, 40000000); if (!Array.isArray(b.rows)) return send(res, 400, { error: "Нет строк" });
          const [ms, me_] = stMonthRange(ym), errors = [], created = [], rows = [], seen = new Set(); let skipped = 0, outside = 0, dups = 0;
          const find = (name, city) => {
            const n = stNorm(name), c = stNorm(city); const same = stCfg.terminals.filter(t => stNorm(t.name) === n);
            if (same.length === 1) return same[0]; if (same.length > 1 && c) return same.find(t => stNorm(t.city) === c) || null; return same.length ? same[0] : null;
          };
          for (let k = 0; k < b.rows.length; k++) {
            const r = b.rows[k] || {}, line = r.line || (k + 2), name = String(r.term || "").trim(), ctn = String(r.ctn || "").trim().toUpperCase().slice(0, 30);
            const size = Number(r.size) === 40 ? 40 : Number(r.size) === 20 ? 20 : 0, inD = stDay(r.inD), outD = r.outD ? stDay(r.outD) : null;
            const bad = !name ? "нет терминала" : !ctn ? "нет номера контейнера" : !size ? "размер должен быть 20 или 40" : inD === null ? "неверная дата заезда" : (r.outD && outD === null) ? "неверная дата выезда" : (outD !== null && outD < inD) ? "выезд раньше заезда" : "";
            if (bad) { skipped++; if (errors.length < 40) errors.push("Строка " + line + ": " + bad); continue; }
            if (inD > me_ || (outD !== null && outD < ms)) { outside++; continue; }
            let tm = find(name, r.city);
            if (!tm) {
              let id; do { id = crypto.randomBytes(4).toString("hex"); } while (stCfg.terminals.some(t => t.id === id));
              tm = stCleanTerm({ city: r.city, name: name.slice(0, 80) }, id); stCfg.terminals.push(tm); created.push(tm.name);
            }
            const dk = tm.id + "|" + ctn + "|" + size + "|" + r.inD + "|" + (outD !== null ? r.outD : "");
            if (seen.has(dk)) { dups++; continue; } seen.add(dk);
            rows.push({ t: tm.id, c: ctn, s: size, i: String(r.inD), o: outD !== null ? String(r.outD) : "" });
          }
          if (!rows.length) return send(res, 400, { error: "Ни одной подходящей строки", errors, outside });
          if (created.length) { stWrite(ST_CFG_F, stCfg); }
          const mf = { month: ym, uploadedAt: Date.now(), by: me.name, terms: stSnapTerms(ym), rows }, result = stCalc(mf, mskToday());
          stWrite(f, mf); stIdx[ym] = stIndexEntry(mf, result); try { writeJson(ST_IDX_F, stIdx); } catch (e) {}
          const noTariff = Object.keys(result.byTerm).filter(id => { const t = result.terms[id]; return t && !t.t20.rate && !t.t40.rate && !t.t20.prr && !t.t40.prr; }).map(id => result.terms[id].name);
          addLogText(me, "Хранение: загрузил(а) данные за " + ym + " (" + rows.length + " строк)"); broadcast("storage", {});
          return send(res, 200, { ok: true, accepted: rows.length, skipped, outside, dups, errors, created, noTariff });
        }
      }
      return send(res, 404, { error: "Не найдено" });
    }
    if (p === "/api/presence" && req.method === "POST") {
      const b = await readBody(req, 1000), key = String(b.key || "").slice(0, 80);
      if (key && b.on !== false) presence.set(me.id, { key, name: me.name, t: Date.now() }); else presence.delete(me.id);
      presenceBroadcast(); return send(res, 200, { ok: true });
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
        let b = await readBody(req, 2 * 1024 * 1024);
        if (!b || typeof b !== "object" || Array.isArray(b)) return send(res, 400, { error: "Неверные данные" });
        if (id === "routes" && me.dept !== "admin") {
          const fa0 = flatten(appDocs.routes || {}, "", {}), fb0 = flatten(b, "", {}), ks = new Set();
          for (const k of new Set(Object.keys(fa0).concat(Object.keys(fb0)))) if (fa0[k] !== fb0[k]) ks.add(/\.fact$/.test(k) ? "fact" : "rail");
          for (const kd of ks) if (deadlineLocked(kd)) return send(res, 403, { error: "Срок внесения истёк (" + fmtDate(ext.deadlines[kd]) + "). Обратитесь к администратору" });
        }
        const pf = partialFields(me, id);
        if (pf) { // меняем только разрешённые поля, всё остальное остаётся как было
          const out = JSON.parse(JSON.stringify(appDocs[id] || {}));
          for (const loc of Object.keys(b)) { if (!b[loc] || typeof b[loc] !== "object") continue; for (const f of pf) if (b[loc][f] !== undefined) { out[loc] = out[loc] || {}; out[loc][f] = Number(b[loc][f]) || 0; } }
          b = out;
        }
        const before = appDocs[id], oldCursor = id === "meta" && before ? before.monthCursor : undefined;
        const changed = JSON.stringify(before) !== JSON.stringify(b);
        appDocs[id] = b; writeJson(path.join(APP_DIR, id + ".json"), b);
        if (changed) { try { recordHistory(me, id, before, b); } catch (e) { console.error("history:", e.message); } }
        broadcast("app", { id, data: b }); addLog(me, id);
        if (changed && me.dept !== "admin" && !pf) {
          const ak = AREA_KIND[id];
          if (ak) {
            let kinds = [ak.kind];
            if (id === "routes") {
              const fa = flatten(before || {}, "", {}), fb = flatten(b, "", {}); kinds = [];
              for (const k of new Set(Object.keys(fa).concat(Object.keys(fb)))) if (fa[k] !== fb[k]) kinds.push(/\.fact$/.test(k) ? "railfact" : "rail");
              kinds = [...new Set(kinds)];
            }
            let mark = false;
            if (kinds.includes("plan")) ext.plansReported = false;
            for (const kd of kinds) { const st = ext.status[ak.dept] && ext.status[ak.dept][kd]; if (st && st.ready && !st.dirty) { st.dirty = true; mark = true; } }
            if (mark) saveExt();
          }
        }
        if (id === "meta" && oldCursor !== undefined && b.monthCursor !== oldCursor) {
          ext.status = {}; ext.deadlines = {}; ext.reminded = {}; ext.plansReported = false; saveExt();
          if (mailCfg.enabled && mailCfg.evCloseRpt) setTimeout(() => { try { sendReport(closeReport()); } catch (e) { console.error("closeReport:", e.message); } }, 20000);
          if (mailCfg.evClosed) mailTo("closed", "Месяц закрыт", "Администратор закрыл месяц и открыл новый. Данные для заполнения обнулены. Сроки нужно задать заново.");
        }
        return send(res, 200, { ok: true });
      }
      if (req.method === "DELETE") {
        { const den2 = writeDenied(me, id); if (den2) return send(res, 403, { error: den2 }); }
        delete appDocs[id]; try { fs.unlinkSync(path.join(APP_DIR, id + ".json")); } catch (e) {}
        broadcast("app", { id, data: null }); return send(res, 200, { ok: true });
      }
    }
    if (p === "/api/snap" && req.method === "POST") {
      if (["viewer", "manager"].includes(me.dept)) return send(res, 403, { error: "Нет прав" });
      const b = await readBody(req, 60000), N = v => Math.round(Number(v) || 0), S = v => String(v == null ? "" : v).slice(0, 80);
      const dirs = o => { const r = {}; Object.keys(DIR_NAMES).forEach(k => { r[k] = N(o && o[k]); }); return r; };
      const names = {}, locs = (Array.isArray(b.locs) ? b.locs : []).slice(0, 100).map(l => { names[S(l.id)] = S(l.n); return { id: S(l.id), n: S(l.n), p: N(l.p), f: N(l.f) }; });
      ext.snap = { t: Date.now(), label: S(b.label), totalVolume: N(b.totalVolume), totalPlan: N(b.totalPlan), totalFact: N(b.totalFact), planByDir: dirs(b.planByDir), factByDir: dirs(b.factByDir), rail: { plan: N(b.rail && b.rail.plan), fact: N(b.rail && b.rail.fact) }, locs, names, plans: {} };
      if (b.plans && typeof b.plans === "object") for (const id of Object.keys(b.plans).slice(0, 100)) { const o = {}; Object.keys(DIR_NAMES).forEach(k => { const q = (b.plans[id] || {})[k] || {}; o[k] = { c20: N(q.c20), c40: N(q.c40) }; }); ext.snap.plans[S(id)] = o; }
      writeJson(EXT_F, ext); return send(res, 200, { ok: true });
    }
    // ---- только администратор ----
    if (me.dept !== "admin") return send(res, 403, { error: "Только администратор" });
    if (p === "/api/history/revert" && req.method === "POST") {
      const b = await readBody(req, 3000), doc = String(b.doc || ""), cellPath = String(b.p || "");
      if (!/^[A-Za-z0-9_]{1,40}$/.test(doc) || !cellPath || doc === "meta" || cellPath === "*") return send(res, 400, { error: "Эту правку вернуть нельзя" });
      const d = appDocs[doc]; if (!d) return send(res, 404, { error: "Раздел не найден" });
      const parts = cellPath.split("."); let o = d;
      for (let i = 0; i < parts.length - 1; i++) { o = o && o[parts[i]]; if (!o || typeof o !== "object") return send(res, 409, { error: "Ячейка не найдена" }); }
      const leaf = parts[parts.length - 1];
      if (String(o[leaf]) !== String(b.to)) return send(res, 409, { error: "Значение уже изменилось после этой правки. Откройте историю заново." });
      const before = JSON.parse(JSON.stringify(d));
      if (b.from === null || b.from === undefined) { if (typeof o[leaf] === "number") o[leaf] = 0; else delete o[leaf]; }
      else o[leaf] = typeof o[leaf] === "number" ? (Number(b.from) || 0) : b.from;
      writeJson(path.join(APP_DIR, doc + ".json"), d);
      try { recordHistory(me, doc, before, d); } catch (e) {}
      broadcast("app", { id: doc, data: d }); addLog(me, doc); addLogText(me, "Вернул(а) значение ячейки (" + doc + ")");
      return send(res, 200, { ok: true });
    }
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
        if (b.subsReset) delete u.subs;
        if (b.subs && typeof b.subs === "object") { u.subs = u.subs || {}; SUB_KEYS.forEach(k => { if (b.subs[k] !== undefined) u.subs[k] = !!b.subs[k]; }); }
        if (b.head !== undefined) { if (b.head) u.head = true; else delete u.head; }
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
      if (b.weeklyDay !== undefined) { const d = parseInt(b.weeklyDay, 10); if (d >= 1 && d <= 7) n.weeklyDay = d; }
      for (const k of ["enabled", "evReady", "evAll", "evClosed", "evRemind", "evWeekly", "evCloseRpt", "evPlans"]) if (b[k] !== undefined) n[k] = !!b[k];
      mailCfg = n; writeJson(MAIL_F, mailCfg); return send(res, 200, { ok: true });
    }
    if (p === "/api/mail/report" && req.method === "POST") {
      if (me.dept !== "admin") return send(res, 403, { error: "Только администратор" });
      const b = await readBody(req, 2000), r = b.type === "close" ? closeReport() : b.type === "plans" ? plansReport() : weeklyReport();
      if (!r) return send(res, 400, { error: b.type === "close" ? "Нет закрытых месяцев в архиве" : "Пока нет данных для отчёта: внесите или измените любое значение в данных" });
      const to = b.type === "plans" ? plansRcpts() : b.type === "close" ? reportRcpts() : weeklyRcpts(); if (!to.length) return send(res, 400, { error: b.type === "plans" ? "Ни у кого не заполнен адрес" : b.type === "close" ? "Не заполнен адрес у администратора, руководителя или отчётности" : "Не заполнен адрес у администратора или руководителя направления (галочка в списке пользователей)" });
      if (!mailCfg.enabled) return send(res, 400, { error: "Отправка уведомлений выключена" });
      await sendReport(r, to); const l = mailLog[0]; return l && !l.ok ? send(res, 400, { error: l.err }) : send(res, 200, { ok: true, to });
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
setInterval(() => { dailyBackup(); remindersCheck(); weeklyCheck(); }, 10 * 60 * 1000);
setTimeout(() => { dailyBackup(); remindersCheck(); }, 5000);
server.listen(PORT, () => console.log("Эвакуация КТК: http://localhost:" + PORT + "  (данные: " + DATA_DIR + ")"));
