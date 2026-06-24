/* ============================================================================
 * PDF Studio — Service Worker
 * Precaches the app shell and its third-party libraries so the editor works
 * fully offline after the first visit. Strategy: cache-first with a network
 * fallback, and navigations fall back to the cached index.html.
 * ========================================================================== */

const CACHE = 'pdf-studio-v3';

const LOCAL_ASSETS = [
  './',
  './index.html',
  './style.css',
  './app.js',
  './manifest.json',
  './icon-192.png',
  './icon-512.png',
  './apple-touch-icon.png'
];

const CDN_ASSETS = [
  'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.min.js',
  'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.worker.min.js',
  'https://cdnjs.cloudflare.com/ajax/libs/pdf-lib/1.17.1/pdf-lib.min.js',
  'https://cdnjs.cloudflare.com/ajax/libs/fabric.js/5.3.1/fabric.min.js',
  'https://cdnjs.cloudflare.com/ajax/libs/Sortable/1.15.6/Sortable.min.js'
];

self.addEventListener('install', (event) => {
  event.waitUntil((async () => {
    const cache = await caches.open(CACHE);
    // Local assets must succeed; CDN assets are added best-effort so a single
    // network hiccup during install cannot break the whole installation.
    await cache.addAll(LOCAL_ASSETS);
    await Promise.allSettled(
      CDN_ASSETS.map((url) =>
        cache.add(new Request(url, { mode: 'cors', credentials: 'omit' }))
      )
    );
    self.skipWaiting();
  })());
});

self.addEventListener('activate', (event) => {
  event.waitUntil((async () => {
    const keys = await caches.keys();
    await Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k)));
    await self.clients.claim();
  })());
});

self.addEventListener('fetch', (event) => {
  const req = event.request;
  if (req.method !== 'GET') return;

  event.respondWith((async () => {
    const cached = await caches.match(req);
    if (cached) return cached;
    try {
      const res = await fetch(req);
      // Opportunistically cache successful same-origin and CDN responses.
      if (res && (res.ok || res.type === 'opaque')) {
        const cache = await caches.open(CACHE);
        cache.put(req, res.clone());
      }
      return res;
    } catch (err) {
      // Offline navigation falls back to the app shell.
      if (req.mode === 'navigate') {
        const shell = await caches.match('./index.html');
        if (shell) return shell;
      }
      throw err;
    }
  })());
});
