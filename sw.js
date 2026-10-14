/* 将棋 — 電波が無くても開けるようにするための小さな仕掛け */
const V = "shogi-v3";
const SHELL = ["./", "./index.html", "./manifest.webmanifest", "./engine.js", "./lessons.js", "./icon-32.png", "./icon-180.png", "./icon-192.png", "./icon-512.png",
               "./se/koma_1.mp3", "./se/koma_2.mp3", "./se/koma_3.mp3", "./se/koma_4.mp3", "./se/koma_5.mp3", "./eval.bin"];

self.addEventListener("install", e => {
  self.skipWaiting();
  e.waitUntil(caches.open(V).then(c => c.addAll(SHELL)).catch(() => {}));
});

self.addEventListener("activate", e => {
  e.waitUntil(
    caches.keys()
      .then(ks => Promise.all(ks.filter(k => k.startsWith("shogi-") && k !== V).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

self.addEventListener("fetch", e => {
  const url = new URL(e.request.url);
  if (url.origin !== location.origin) return;          // 文字の書体などの外部通信は素通し
  if (e.request.method !== "GET") return;

  // 本体は「まず新しいものを取りに行く」。取れなければ手元の控えを出す
  if (e.request.mode === "navigate") {
    e.respondWith(
      fetch(e.request)
        .then(r => { const c = r.clone(); caches.open(V).then(x => x.put("./index.html", c)); return r; })
        .catch(() => caches.match("./index.html").then(r => r || caches.match("./")))
    );
    return;
  }
  // 頭脳（engine.js）なども、直したときすぐ届くように「まず新しいもの」。取れなければ控え
  e.respondWith(
    fetch(e.request)
      .then(r => { const c = r.clone(); caches.open(V).then(x => x.put(e.request, c)); return r; })
      .catch(() => caches.match(e.request))
  );
});
