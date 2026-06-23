/* ============================================================================
 * PDF Studio — app.js
 * A fully client-side PDF editor. No network calls, no servers, no tracking.
 *
 * Pipeline overview
 *   - PDF.js renders page backgrounds to <canvas> (display only).
 *   - Fabric.js hosts a transparent annotation layer on top of each page.
 *   - pdf-lib assembles the exported document (copy/rotate/blank/image pages)
 *     and bakes the annotation layer back in as a high-resolution PNG overlay.
 *   - A tiny built-in store-only ZIP writer bundles "split" output.
 *
 * Coordinate model
 *   - 1 PDF point == BASE backing pixels inside the editor canvases.
 *   - Annotations are stored in those backing pixels (Fabric JSON).
 *   - On export they are rasterised at BASE*EXPORT_MULT, then counter-rotated
 *     so that the page's own /Rotate re-aligns them with the visible content.
 * ========================================================================== */

(() => {
  'use strict';

  /* ----------------------------- Library handles ------------------------- */
  const { PDFDocument, degrees, StandardFonts, rgb } = PDFLib;
  pdfjsLib.GlobalWorkerOptions.workerSrc =
    'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.worker.min.js';

  /* Feature-detect encryption. The bundled pdf-lib build has no encrypt()
     method, so password protection is disabled gracefully rather than faked. */
  const ENCRYPT_SUPPORTED = typeof PDFDocument.prototype.encrypt === 'function';

  /* ------------------------------- Constants ----------------------------- */
  const BASE = 2;            // backing pixels per PDF point in the editor
  const EXPORT_MULT = 2;     // annotation raster multiplier (~288 dpi)
  const PT2CSS = 96 / 72;    // CSS pixels per point at 100% zoom
  const MAX_IMG_PT = 1600;   // largest image-page dimension, in points
  const CONT_SCALE = 1.6;    // continuous-view backing pixels per point
  const HIST_CAP = 40;       // per-page undo snapshots
  const ZOOM_MIN = 10, ZOOM_MAX = 800;
  const FABRIC_PROPS = [];   // extra props to persist (defaults are enough)
  const TOOL_LABEL = {
    select: 'Select', text: 'Text', draw: 'Draw',
    rect: 'Rectangle', ellipse: 'Circle', arrow: 'Arrow'
  };

  /* --------------------------------- State ------------------------------- */
  const sources = new Map();   // id -> { bytes, libDoc, pdfjs }
  let pages = [];              // ordered array of page objects
  let active = 0;
  let viewMode = 'single';     // 'single' | 'continuous'
  let zoomPct = 100;
  let fitMode = null;          // null | 'width' | 'page'
  let tool = 'select';
  let suppressHistory = false;
  let numberCfg = { enabled: false, format: '{n}', pos: 'bc', size: 11, start: 1, color: '#333333' };
  let uid = 0;
  const nextId = () => 'id' + (++uid);

  let fcanvas = null;          // the live Fabric canvas (single-page editor)
  let draft = null, startPt = null;
  let sortable = null, thumbObserver = null, contObserver = null;
  let busyEl = null;

  /* --------------------------------- DOM --------------------------------- */
  const $ = (id) => document.getElementById(id);
  const stage = $('stage'), stageSizer = $('stageSizer'), stageWrap = $('stageWrap');
  const bgCanvas = $('bgCanvas');
  const viewer = $('viewer'), continuous = $('continuous'), empty = $('empty');
  const thumbs = $('thumbs'), thumbCount = $('thumbCount'), selAll = $('selAll');
  const zoomVal = $('zoomVal');
  const inColor = $('inColor'), inThick = $('inThick');
  const statusPage = $('statusPage'), statusTool = $('statusTool'), statusOffline = $('statusOffline'), statusMsg = $('statusMsg');

  /* ------------------------------- Utilities ----------------------------- */
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  const copyBytes = (u8) => u8.slice(0);

  function toast(msg, isErr) {
    const host = $('toasts');
    const t = document.createElement('div');
    t.className = 'toast' + (isErr ? ' err' : '');
    t.textContent = msg;
    host.appendChild(t);
    setTimeout(() => { t.style.opacity = '0'; t.style.transition = 'opacity .3s'; }, 2200);
    setTimeout(() => t.remove(), 2600);
  }

  function busy(on, msg) {
    document.body.style.cursor = on ? 'progress' : '';
    if (on) {
      if (!busyEl) {
        busyEl = document.createElement('div');
        busyEl.className = 'busy';
        busyEl.innerHTML = '<div class="busy-box"><span class="spin"></span><span class="busy-msg"></span></div>';
        document.body.appendChild(busyEl);
      }
      busyEl.querySelector('.busy-msg').textContent = msg || 'Working\u2026';
      busyEl.hidden = false;
    } else if (busyEl) {
      busyEl.hidden = true;
    }
  }

  function saveBlob(blob, name) {
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url; a.download = name;
    document.body.appendChild(a); a.click();
    setTimeout(() => { URL.revokeObjectURL(url); a.remove(); }, 1500);
  }

  function loadImage(url) {
    return new Promise((res, rej) => {
      const img = new Image();
      img.onload = () => res(img);
      img.onerror = rej;
      img.src = url;
    });
  }

  function hexToRgb(hex) {
    const m = /^#?([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})$/i.exec(hex || '#000000');
    if (!m) return { r: 0, g: 0, b: 0 };
    return { r: parseInt(m[1], 16) / 255, g: parseInt(m[2], 16) / 255, b: parseInt(m[3], 16) / 255 };
  }

  async function canvasToPngBytes(canvas) {
    const blob = await new Promise(r => canvas.toBlob(r, 'image/png'));
    return new Uint8Array(await blob.arrayBuffer());
  }

  /* ------------------------- Built-in store-only ZIP --------------------- */
  function crc32(buf) {
    const table = crc32.t || (crc32.t = (() => {
      const t = []; for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t;
    })());
    let crc = 0xFFFFFFFF;
    for (let i = 0; i < buf.length; i++) crc = (crc >>> 8) ^ table[(crc ^ buf[i]) & 0xFF];
    return (crc ^ 0xFFFFFFFF) >>> 0;
  }
  const strBytes = (s) => { const a = new Uint8Array(s.length); for (let i = 0; i < s.length; i++) a[i] = s.charCodeAt(i) & 0xff; return a; };
  const u16 = (n) => new Uint8Array([n & 0xff, (n >>> 8) & 0xff]);
  const u32 = (n) => new Uint8Array([n & 0xff, (n >>> 8) & 0xff, (n >>> 16) & 0xff, (n >>> 24) & 0xff]);
  function concatBytes(chunks) {
    const len = chunks.reduce((a, c) => a + c.length, 0);
    const out = new Uint8Array(len); let o = 0;
    for (const c of chunks) { out.set(c, o); o += c.length; }
    return out;
  }
  function createZip(files) { // files: [{ name, data: Uint8Array }]
    const locals = [], centrals = []; let offset = 0;
    for (const f of files) {
      const nameBytes = strBytes(f.name), data = f.data, crc = crc32(data);
      const local = concatBytes([u32(0x04034b50), u16(20), u16(0), u16(0), u16(0), u16(0), u32(crc), u32(data.length), u32(data.length), u16(nameBytes.length), u16(0), nameBytes, data]);
      locals.push(local);
      const central = concatBytes([u32(0x02014b50), u16(20), u16(20), u16(0), u16(0), u16(0), u16(0), u32(crc), u32(data.length), u32(data.length), u16(nameBytes.length), u16(0), u16(0), u16(0), u16(0), u32(0), u32(offset), nameBytes]);
      centrals.push(central); offset += local.length;
    }
    const centralStart = offset, centralBlock = concatBytes(centrals), centralSize = centralBlock.length;
    const end = concatBytes([u32(0x06054b50), u16(0), u16(0), u16(files.length), u16(files.length), u32(centralSize), u32(centralStart), u16(0)]);
    return concatBytes([...locals, centralBlock, end]);
  }

  /* ------------------------------ Source model --------------------------- */
  async function addSource(srcBytes) {
    const bytes = copyBytes(srcBytes);
    const id = nextId();
    // PDF.js detaches the buffer it is given, so each consumer gets its own copy.
    const libDoc = await PDFDocument.load(copyBytes(bytes), { ignoreEncryption: true });
    const pdfjs = await pdfjsLib.getDocument({ data: copyBytes(bytes) }).promise;
    sources.set(id, { bytes, libDoc, pdfjs });
    return id;
  }

  async function pagesFromSource(id) {
    const src = sources.get(id);
    const n = src.pdfjs.numPages;
    const out = [];
    for (let i = 0; i < n; i++) {
      const pg = await src.pdfjs.getPage(i + 1);
      const vp = pg.getViewport({ scale: 1, rotation: 0 });
      out.push({
        id: nextId(), kind: 'pdf', sourceId: id, sourcePageIndex: i,
        baseRotate: pg.rotate || 0, pdfW: vp.width, pdfH: vp.height,
        rotation: 0, annJSON: null, _hist: [], _hidx: -1, _proxy: pg
      });
    }
    return out;
  }

  function blankPage(wPt, hPt) {
    return { id: nextId(), kind: 'blank', width: wPt, height: hPt, rotation: 0, annJSON: null, _hist: [], _hidx: -1 };
  }

  async function imagePageFromFile(file) {
    const type = file.type;
    let bytes = new Uint8Array(await file.arrayBuffer());
    let kind = type === 'image/png' ? 'png' : type === 'image/jpeg' ? 'jpg' : 'webp';
    const url = URL.createObjectURL(new Blob([bytes], { type }));
    const img = await loadImage(url);
    let imgW = img.naturalWidth, imgH = img.naturalHeight;
    if (kind === 'webp') {
      // WEBP is not embeddable by pdf-lib; convert to PNG once at import.
      const c = document.createElement('canvas'); c.width = imgW; c.height = imgH;
      c.getContext('2d').drawImage(img, 0, 0);
      const blob = await new Promise(r => c.toBlob(r, 'image/png'));
      bytes = new Uint8Array(await blob.arrayBuffer());
      kind = 'png';
    }
    URL.revokeObjectURL(url);
    return { id: nextId(), kind: 'image', imageBytes: bytes, imageType: kind, imgW, imgH, _imgEl: null, rotation: 0, annJSON: null, _hist: [], _hidx: -1 };
  }

  function getImageEl(page) {
    if (page._imgEl) return Promise.resolve(page._imgEl);
    return new Promise((res, rej) => {
      const mime = page.imageType === 'png' ? 'image/png' : 'image/jpeg';
      const url = URL.createObjectURL(new Blob([page.imageBytes], { type: mime }));
      const img = new Image();
      img.onload = () => { page._imgEl = img; URL.revokeObjectURL(url); res(img); };
      img.onerror = (e) => { URL.revokeObjectURL(url); rej(e); };
      img.src = url;
    });
  }

  /* ------------------------------- Geometry ------------------------------ */
  function getTotalRotation(page) {
    if (page.kind === 'pdf') return ((page.baseRotate || 0) + page.rotation) % 360;
    return ((page.rotation % 360) + 360) % 360;
  }

  function imagePagePoints(page) {
    let w = page.imgW, h = page.imgH;
    const m = Math.max(w, h);
    if (m > MAX_IMG_PT) { const s = MAX_IMG_PT / m; w *= s; h *= s; }
    return { w, h };
  }

  function unrotatedSizePt(page) {
    if (page.kind === 'pdf') return { w: page.pdfW, h: page.pdfH };
    if (page.kind === 'image') return imagePagePoints(page);
    return { w: page.width, h: page.height };
  }

  function displaySizePt(page) {
    const rot = getTotalRotation(page);
    const u = unrotatedSizePt(page);
    return (rot === 90 || rot === 270) ? { w: u.h, h: u.w } : { w: u.w, h: u.h };
  }

  /* ------------------------------- Painting ------------------------------ */
  function drawRotatedImage(ctx, img, cw, ch, rot) {
    ctx.save();
    ctx.translate(cw / 2, ch / 2);
    ctx.rotate(rot * Math.PI / 180);
    let dw, dh;
    if (rot === 90 || rot === 270) { dw = ch; dh = cw; } else { dw = cw; dh = ch; }
    ctx.drawImage(img, -dw / 2, -dh / 2, dw, dh);
    ctx.restore();
  }

  // Paint a page background onto `canvas` at `scale` (backing px per point).
  async function paintPage(page, canvas, scale) {
    const disp = displaySizePt(page);
    const cw = Math.max(1, Math.round(disp.w * scale));
    const ch = Math.max(1, Math.round(disp.h * scale));
    canvas.width = cw; canvas.height = ch;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = '#fff'; ctx.fillRect(0, 0, cw, ch);
    const rot = getTotalRotation(page);
    if (page.kind === 'pdf') {
      const src = sources.get(page.sourceId);
      const pg = page._proxy || await src.pdfjs.getPage(page.sourcePageIndex + 1);
      page._proxy = pg;
      const vp = pg.getViewport({ scale, rotation: rot });
      await pg.render({ canvasContext: ctx, viewport: vp }).promise;
    } else if (page.kind === 'image') {
      const img = await getImageEl(page);
      drawRotatedImage(ctx, img, cw, ch, rot);
    }
    // blank pages are already white
  }

  /* ----------------------- Annotation rasterisation ---------------------- */
  // Render a page's stored annotations into a detached canvas (display
  // orientation) at the given backing-pixel zoom (relative to BASE).
  function flattenAnnotations(page, zoomFromBase) {
    return new Promise((res) => {
      if (!page.annJSON) return res(null);
      const disp = displaySizePt(page);
      const w = Math.max(1, Math.round(disp.w * BASE * zoomFromBase));
      const h = Math.max(1, Math.round(disp.h * BASE * zoomFromBase));
      const el = document.createElement('canvas'); el.width = w; el.height = h;
      const sc = new fabric.StaticCanvas(el, { enableRetinaScaling: false });
      sc.setDimensions({ width: w, height: h });
      sc.setZoom(zoomFromBase);
      sc.loadFromJSON(page.annJSON, () => {
        sc.renderAll();
        const out = document.createElement('canvas'); out.width = w; out.height = h;
        out.getContext('2d').drawImage(sc.lowerCanvasEl, 0, 0);
        sc.dispose();
        res(out);
      });
    });
  }

  function rotateCanvas(src, deg) {
    deg = ((deg % 360) + 360) % 360;
    if (deg === 0 || !src) return src;
    const swap = (deg === 90 || deg === 270);
    const w = src.width, h = src.height;
    const ow = swap ? h : w, oh = swap ? w : h;
    const out = document.createElement('canvas'); out.width = ow; out.height = oh;
    const ctx = out.getContext('2d');
    ctx.translate(ow / 2, oh / 2);
    ctx.rotate(deg * Math.PI / 180);
    ctx.drawImage(src, -w / 2, -h / 2);
    return out;
  }

  /* -------------------------------- Export ------------------------------- */
  async function buildPdf(indices) {
    const out = await PDFDocument.create();
    const helv = await out.embedFont(StandardFonts.Helvetica);

    for (let k = 0; k < indices.length; k++) {
      const page = pages[indices[k]];
      let pg;

      if (page.kind === 'pdf') {
        const src = sources.get(page.sourceId);
        const [cp] = await out.copyPages(src.libDoc, [page.sourcePageIndex]);
        pg = out.addPage(cp);
        pg.setRotation(degrees(getTotalRotation(page)));
      } else if (page.kind === 'blank') {
        pg = out.addPage([page.width, page.height]);
        if (page.rotation % 360) pg.setRotation(degrees(getTotalRotation(page)));
      } else { // image
        const fit = imagePagePoints(page);
        pg = out.addPage([fit.w, fit.h]);
        const img = page.imageType === 'png'
          ? await out.embedPng(page.imageBytes)
          : await out.embedJpg(page.imageBytes);
        pg.drawImage(img, { x: 0, y: 0, width: fit.w, height: fit.h });
        if (page.rotation % 360) pg.setRotation(degrees(getTotalRotation(page)));
      }

      // Bake annotations: rasterise in display orientation, then counter-rotate
      // so the page's own /Rotate brings them back into view aligned.
      const annCanvas = await flattenAnnotations(page, EXPORT_MULT);
      if (annCanvas) {
        const T = getTotalRotation(page);
        const counter = rotateCanvas(annCanvas, (360 - T) % 360);
        const png = await out.embedPng(await canvasToPngBytes(counter));
        const sz = pg.getSize(); // unrotated mediabox
        pg.drawImage(png, { x: 0, y: 0, width: sz.width, height: sz.height });
      }
    }

    // Page numbers (crisp vector text in page coordinate space).
    if (numberCfg.enabled) {
      const total = out.getPageCount();
      const col = hexToRgb(numberCfg.color);
      const size = numberCfg.size, margin = 28;
      for (let i = 0; i < total; i++) {
        const pg = out.getPage(i);
        const label = numberCfg.format
          .replace(/\{n\}/g, String(i + Number(numberCfg.start)))
          .replace(/\{total\}/g, String(total));
        const tw = helv.widthOfTextAtSize(label, size);
        const { width, height } = pg.getSize();
        const vert = numberCfg.pos[0], horiz = numberCfg.pos[1];
        let x = (width - tw) / 2;
        if (horiz === 'l') x = margin; else if (horiz === 'r') x = width - margin - tw;
        let y = margin;
        if (vert === 't') y = height - margin - size;
        pg.drawText(label, { x, y, size, font: helv, color: rgb(col.r, col.g, col.b) });
      }
    }

    return await out.save();
  }

  /* ------------------------------- Fabric -------------------------------- */
  function ensureFabric() {
    if (fcanvas) return;
    fcanvas = new fabric.Canvas('fabricCanvas', {
      enableRetinaScaling: false,
      preserveObjectStacking: true,
      selection: true
    });
    wireFabricEvents();
  }

  function wireFabricEvents() {
    fcanvas.on('mouse:down', (opt) => {
      if (tool === 'select' || tool === 'draw') return;
      const p = fcanvas.getPointer(opt.e);
      startPt = p;
      if (tool === 'text') {
        const t = new fabric.IText('Text', {
          left: p.x, top: p.y, fontFamily: 'Helvetica, Arial, sans-serif',
          fontSize: Math.max(16, +inThick.value * 5), fill: inColor.value
        });
        fcanvas.add(t); fcanvas.setActiveObject(t);
        setTool('select'); t.enterEditing(); t.selectAll();
        startPt = null;
        return;
      }
      if (tool === 'rect') {
        draft = new fabric.Rect({ left: p.x, top: p.y, width: 1, height: 1, fill: 'transparent', stroke: inColor.value, strokeWidth: +inThick.value, strokeUniform: true });
      } else if (tool === 'ellipse') {
        draft = new fabric.Ellipse({ left: p.x, top: p.y, rx: 1, ry: 1, fill: 'transparent', stroke: inColor.value, strokeWidth: +inThick.value, strokeUniform: true });
      } else if (tool === 'arrow') {
        draft = new fabric.Line([p.x, p.y, p.x, p.y], { stroke: inColor.value, strokeWidth: +inThick.value, strokeLineCap: 'round' });
      }
      if (draft) fcanvas.add(draft);
    });

    fcanvas.on('mouse:move', (opt) => {
      if (!draft || !startPt) return;
      const p = fcanvas.getPointer(opt.e);
      if (tool === 'rect') {
        draft.set({ left: Math.min(p.x, startPt.x), top: Math.min(p.y, startPt.y), width: Math.abs(p.x - startPt.x), height: Math.abs(p.y - startPt.y) });
      } else if (tool === 'ellipse') {
        draft.set({ left: Math.min(p.x, startPt.x), top: Math.min(p.y, startPt.y), rx: Math.abs(p.x - startPt.x) / 2, ry: Math.abs(p.y - startPt.y) / 2 });
      } else if (tool === 'arrow') {
        draft.set({ x2: p.x, y2: p.y });
      }
      fcanvas.renderAll();
    });

    fcanvas.on('mouse:up', () => {
      if (!draft) return;
      if (tool === 'arrow') {
        const { x1, y1, x2, y2 } = draft;
        fcanvas.remove(draft);
        if (Math.hypot(x2 - x1, y2 - y1) > 4) {
          const g = buildArrowGroup(x1, y1, x2, y2, draft.stroke, draft.strokeWidth);
          fcanvas.add(g); fcanvas.setActiveObject(g); pushHistory();
        }
      } else {
        const tiny = draft.width < 3 && draft.height < 3 && !draft.rx;
        const tinyE = draft.rx != null && draft.rx < 2 && draft.ry < 2;
        if (tiny || tinyE) { fcanvas.remove(draft); }
        else { fcanvas.setActiveObject(draft); pushHistory(); }
      }
      draft = null; startPt = null;
      setTool('select');
    });

    fcanvas.on('path:created', () => { if (!suppressHistory) pushHistory(); });
    fcanvas.on('object:added', (e) => { if (!suppressHistory && !draft && e.target && e.target.type !== 'path') pushHistory(); });
    fcanvas.on('object:modified', () => { if (!suppressHistory) pushHistory(); });
    fcanvas.on('object:removed', () => { if (!suppressHistory) pushHistory(); });
    fcanvas.on('selection:created', updateObjButtons);
    fcanvas.on('selection:updated', updateObjButtons);
    fcanvas.on('selection:cleared', updateObjButtons);
  }

  function buildArrowGroup(x1, y1, x2, y2, color, width) {
    const angle = Math.atan2(y2 - y1, x2 - x1);
    const headLen = Math.max(12, width * 3.5);
    const line = new fabric.Line([x1, y1, x2, y2], { stroke: color, strokeWidth: width, strokeLineCap: 'round' });
    const head = new fabric.Triangle({
      left: x2, top: y2, originX: 'center', originY: 'center',
      width: headLen, height: headLen, fill: color,
      angle: angle * 180 / Math.PI + 90
    });
    return new fabric.Group([line, head]);
  }

  function applyStyleToObj(o, color, width) {
    const setOne = (obj) => {
      const isText = obj.type === 'i-text' || obj.type === 'text' || obj.type === 'textbox';
      if (isText) {
        if (color != null) obj.set('fill', color);
      } else {
        if (color != null && obj.stroke != null) obj.set('stroke', color);
        if (color != null && (obj.type === 'triangle' || (obj.fill && obj.fill !== 'transparent' && obj.type !== 'image'))) obj.set('fill', color);
        if (width != null && obj.strokeWidth != null) obj.set('strokeWidth', width);
      }
    };
    if (o.type === 'group') o.getObjects().forEach(setOne); else setOne(o);
  }

  /* ------------------------------- History ------------------------------- */
  function pushHistory() {
    const page = pages[active]; if (!page || !fcanvas) return;
    const snap = JSON.stringify(fcanvas.toJSON(FABRIC_PROPS));
    if (page._hist[page._hidx] === snap) return;
    page._hist = page._hist.slice(0, page._hidx + 1);
    page._hist.push(snap);
    if (page._hist.length > HIST_CAP) page._hist.shift();
    page._hidx = page._hist.length - 1;
    page.annJSON = JSON.parse(snap);
    invalidateThumb(page);
    updateUndoRedo();
  }

  function seedHistory(page) {
    const snap = JSON.stringify(fcanvas.toJSON(FABRIC_PROPS));
    page._hist = [snap]; page._hidx = 0;
    updateUndoRedo();
  }

  function undo() {
    const page = pages[active]; if (!page || page._hidx <= 0) return;
    page._hidx--; restoreSnap(page);
  }
  function redo() {
    const page = pages[active]; if (!page || page._hidx >= page._hist.length - 1) return;
    page._hidx++; restoreSnap(page);
  }
  function restoreSnap(page) {
    const snap = page._hist[page._hidx];
    page.annJSON = JSON.parse(snap);
    suppressHistory = true;
    fcanvas.loadFromJSON(snap, () => {
      fcanvas.renderAll(); suppressHistory = false;
      applyToolState(); updateUndoRedo(); invalidateThumb(page);
    });
  }

  function updateUndoRedo() {
    const page = pages[active];
    $('btnUndo').disabled = !page || page._hidx <= 0;
    $('btnRedo').disabled = !page || !page._hist || page._hidx >= page._hist.length - 1;
  }
  function updateObjButtons() {
    $('btnDeleteObj').disabled = !(fcanvas && fcanvas.getActiveObject());
  }

  /* --------------------------------- Tools ------------------------------- */
  function setTool(t) {
    tool = t;
    document.querySelectorAll('.tbtn.tool').forEach(b => b.classList.toggle('active', b.dataset.tool === t));
    statusTool.textContent = TOOL_LABEL[t] || 'Select';
    applyToolState();
  }
  function applyToolState() {
    if (!fcanvas) return;
    const drawing = tool === 'draw';
    fcanvas.isDrawingMode = drawing;
    if (drawing) {
      fcanvas.freeDrawingBrush = new fabric.PencilBrush(fcanvas);
      fcanvas.freeDrawingBrush.color = inColor.value;
      fcanvas.freeDrawingBrush.width = +inThick.value;
    }
    const selectMode = tool === 'select';
    fcanvas.selection = selectMode;
    fcanvas.defaultCursor = selectMode ? 'default' : 'crosshair';
    fcanvas.forEachObject(o => { o.selectable = selectMode; o.evented = selectMode; });
    if (!selectMode) fcanvas.discardActiveObject();
    fcanvas.requestRenderAll();
  }

  /* ------------------------- Single-page rendering ----------------------- */
  function loadAnn(page) {
    return new Promise((res) => {
      fcanvas.clear();
      if (page.annJSON) {
        suppressHistory = true;
        fcanvas.loadFromJSON(page.annJSON, () => { fcanvas.renderAll(); suppressHistory = false; res(); });
      } else { fcanvas.renderAll(); res(); }
    });
  }

  async function renderActive() {
    if (!pages.length) { updateChrome(); return; }
    ensureFabric();
    const page = pages[active];
    await paintPage(page, bgCanvas, BASE);
    const bw = bgCanvas.width, bh = bgCanvas.height;
    stage.style.width = bw + 'px';
    stage.style.height = bh + 'px';
    fcanvas.setDimensions({ width: bw, height: bh });
    await loadAnn(page);
    if (!page._hist.length) seedHistory(page);
    applyToolState();
    if (fitMode) recomputeFit(); else applyZoom();
    updateChrome();
    updatePageStatus();
    updateUndoRedo();
    updateObjButtons();
  }

  function applyZoom() {
    if (!pages.length) return;
    const disp = displaySizePt(pages[active]);
    const bw = disp.w * BASE, bh = disp.h * BASE;
    const cssScale = (zoomPct / 100) * PT2CSS / BASE;
    stageSizer.style.width = (bw * cssScale) + 'px';
    stageSizer.style.height = (bh * cssScale) + 'px';
    stage.style.transform = 'scale(' + cssScale + ')';
    zoomVal.textContent = Math.round(zoomPct) + '%';
    if (fcanvas) fcanvas.calcOffset();
  }

  function recomputeFit() {
    if (!fitMode || !pages.length || viewMode !== 'single') return;
    const disp = displaySizePt(pages[active]);
    const avail = stageWrap.clientWidth - 72;
    const availH = stageWrap.clientHeight - 72;
    const pw = disp.w * PT2CSS, ph = disp.h * PT2CSS;
    let z = (fitMode === 'width') ? (avail / pw) : Math.min(avail / pw, availH / ph);
    zoomPct = clamp(z * 100, ZOOM_MIN, ZOOM_MAX);
    applyZoom();
  }

  /* --------------------------- Continuous view --------------------------- */
  function buildContinuous() {
    continuous.innerHTML = '';
    if (contObserver) contObserver.disconnect();
    contObserver = new IntersectionObserver((entries) => {
      entries.forEach(en => { if (en.isIntersecting) renderCont(en.target); });
    }, { root: viewer, rootMargin: '300px 0px' });

    pages.forEach((page, i) => {
      const wrap = document.createElement('div');
      wrap.className = 'cpage' + (i === active ? ' active' : '');
      wrap.dataset.idx = i;
      const cv = document.createElement('canvas');
      const label = document.createElement('div');
      label.className = 'clabel'; label.textContent = 'Page ' + (i + 1);
      wrap.appendChild(cv); wrap.appendChild(label);
      wrap._page = page; wrap._canvas = cv; wrap._rendered = false;
      sizeContWrap(wrap);
      wrap.addEventListener('click', () => { setViewMode('single'); setActive(i); });
      continuous.appendChild(wrap);
      contObserver.observe(wrap);
    });
  }

  function sizeContWrap(wrap) {
    const disp = displaySizePt(wrap._page);
    const cssScale = (zoomPct / 100) * PT2CSS;
    const w = disp.w * cssScale, h = disp.h * cssScale;
    wrap.style.width = w + 'px'; wrap.style.height = h + 'px';
    wrap._canvas.style.width = w + 'px'; wrap._canvas.style.height = h + 'px';
  }

  async function renderCont(wrap) {
    if (wrap._rendered) return;
    wrap._rendered = true;
    const page = wrap._page, cv = wrap._canvas;
    await paintPage(page, cv, CONT_SCALE);
    const ann = await flattenAnnotations(page, CONT_SCALE / BASE);
    if (ann) cv.getContext('2d').drawImage(ann, 0, 0);
    sizeContWrap(wrap);
  }

  function zoomContinuous() {
    [...continuous.children].forEach(sizeContWrap);
    zoomVal.textContent = Math.round(zoomPct) + '%';
  }

  /* ------------------------------ Thumbnails ----------------------------- */
  function rebuildThumbs() {
    thumbs.innerHTML = '';
    if (thumbObserver) thumbObserver.disconnect();
    thumbObserver = new IntersectionObserver((entries) => {
      entries.forEach(en => { if (en.isIntersecting) renderThumb(en.target); });
    }, { root: thumbs, rootMargin: '200px 0px' });

    pages.forEach((page, i) => {
      const li = document.createElement('li');
      li.className = 'thumb' + (i === active ? ' active' : '');
      li.dataset.id = page.id;
      const pick = document.createElement('input');
      pick.type = 'checkbox'; pick.className = 'pick'; pick.title = 'Select page';
      const cv = document.createElement('canvas');
      const pno = document.createElement('span'); pno.className = 'pno'; pno.textContent = i + 1;
      li.appendChild(pick); li.appendChild(cv); li.appendChild(pno);
      li._page = page; li._canvas = cv; li._rendered = false;
      cv.addEventListener('click', () => setActive(i));
      pick.addEventListener('change', syncSelAll);
      thumbs.appendChild(li);
      thumbObserver.observe(li);
    });
    thumbCount.textContent = pages.length + (pages.length === 1 ? ' page' : ' pages');
    initSortable();
    syncSelAll();
  }

  async function renderThumb(li) {
    if (li._rendered) return; li._rendered = true;
    try {
      const disp = displaySizePt(li._page);
      const scale = clamp(150 / disp.w, 0.05, 1.2);
      await paintPage(li._page, li._canvas, scale);
      // Let the thumbnail keep the real page proportions.
      li._canvas.style.removeProperty('aspect-ratio');
      li._canvas.style.removeProperty('object-fit');
      li._canvas.style.height = 'auto';
    } catch (e) { /* ignore individual thumb failures */ }
  }

  function invalidateThumb(page) {
    const li = [...thumbs.children].find(el => el._page === page);
    if (li) { li._rendered = false; if (isInView(li)) renderThumb(li); }
  }
  function isInView(el) {
    const r = el.getBoundingClientRect(), pr = thumbs.getBoundingClientRect();
    return r.bottom > pr.top - 200 && r.top < pr.bottom + 200;
  }

  function highlightThumb() {
    [...thumbs.children].forEach((li, i) => li.classList.toggle('active', i === active));
    [...continuous.children].forEach((w, i) => w.classList.toggle('active', i === active));
  }

  function initSortable() {
    if (sortable) sortable.destroy();
    sortable = Sortable.create(thumbs, {
      animation: 150, draggable: 'li.thumb', filter: '.pick',
      onEnd: () => {
        const order = [...thumbs.children].map(li => li.dataset.id);
        const map = new Map(pages.map(p => [p.id, p]));
        const activeId = pages[active] && pages[active].id;
        pages = order.map(id => map.get(id)).filter(Boolean);
        active = Math.max(0, pages.findIndex(p => p.id === activeId));
        rebuildThumbs();
        if (viewMode === 'single') renderActive(); else buildContinuous();
        toast('Pages reordered');
      }
    });
  }

  /* ------------------------------ Selection ------------------------------ */
  function selectedIndices() {
    const out = [];
    [...thumbs.children].forEach((li, i) => { if (li.querySelector('.pick').checked) out.push(i); });
    return out;
  }
  function syncSelAll() {
    const boxes = [...thumbs.querySelectorAll('.pick')];
    const checked = boxes.filter(b => b.checked).length;
    selAll.checked = boxes.length > 0 && checked === boxes.length;
    selAll.indeterminate = checked > 0 && checked < boxes.length;
  }

  /* ----------------------------- View / chrome --------------------------- */
  function updateChrome() {
    const has = pages.length > 0;
    empty.style.display = has ? 'none' : 'grid';
    stageWrap.style.display = (has && viewMode === 'single') ? 'flex' : 'none';
    continuous.style.display = (has && viewMode === 'continuous') ? 'flex' : 'none';
  }
  function updatePageStatus() {
    statusPage.textContent = pages.length ? ('Page ' + (active + 1) + ' / ' + pages.length) : '\u2014';
  }

  async function setViewMode(mode) {
    if (mode === viewMode) return;
    if (mode === 'continuous') commitActiveAnn();
    viewMode = mode;
    updateChrome();
    if (mode === 'continuous') buildContinuous();
    else await renderActive();
  }

  async function setActive(i) {
    if (!pages.length) return;
    if (viewMode === 'single') commitActiveAnn();
    active = clamp(i, 0, pages.length - 1);
    highlightThumb();
    if (viewMode === 'single') await renderActive();
    updatePageStatus();
  }

  function commitActiveAnn() {
    if (viewMode === 'single' && fcanvas && pages[active]) {
      pages[active].annJSON = fcanvas.toJSON(FABRIC_PROPS);
    }
  }

  /* ------------------------------ Operations ----------------------------- */
  function sizePresetPt(size, orient) {
    const map = { a4: [595.28, 841.89], letter: [612, 792], legal: [612, 1008], a5: [419.53, 595.28] };
    let [w, h] = map[size] || map.a4;
    if (orient === 'landscape') [w, h] = [h, w];
    return { w, h };
  }

  async function doNewBlank(size, orient) {
    const { w, h } = sizePresetPt(size, orient);
    resetDocument();
    pages = [blankPage(w, h)];
    active = 0;
    afterDocChange();
    toast('Blank document created');
  }

  function resetDocument() {
    sources.clear();
    pages = []; active = 0;
    if (fcanvas) { fcanvas.clear(); }
  }

  async function openFiles(fileList, { merge }) {
    const files = [...fileList].filter(f => f.type === 'application/pdf' || /\.pdf$/i.test(f.name));
    if (!files.length) return;
    busy(true, 'Opening\u2026');
    try {
      if (!merge) resetDocument();
      for (const f of files) {
        const id = await addSource(new Uint8Array(await f.arrayBuffer()));
        const ps = await pagesFromSource(id);
        pages.push(...ps);
      }
      active = merge ? active : 0;
      afterDocChange();
      toast(files.length > 1 ? (files.length + ' PDFs loaded') : 'PDF loaded');
    } catch (e) {
      console.error(e); toast('Could not open PDF', true);
    } finally { busy(false); }
  }

  async function addImagesAsPages(fileList) {
    const files = [...fileList].filter(f => /^image\/(png|jpeg|webp)$/.test(f.type));
    if (!files.length) return;
    busy(true, 'Importing images\u2026');
    try {
      const first = pages.length === 0;
      for (const f of files) pages.push(await imagePageFromFile(f));
      if (first) active = 0;
      afterDocChange();
      toast(files.length > 1 ? (files.length + ' images added') : 'Image added');
    } catch (e) { console.error(e); toast('Could not import images', true); }
    finally { busy(false); }
  }

  async function insertFromFile(file) {
    if (!file) return;
    busy(true, 'Inserting\u2026');
    try {
      const id = await addSource(new Uint8Array(await file.arrayBuffer()));
      const ps = await pagesFromSource(id);
      const at = pages.length ? active + 1 : 0;
      pages.splice(at, 0, ...ps);
      active = at;
      afterDocChange();
      toast(ps.length + ' page(s) inserted');
    } catch (e) { console.error(e); toast('Could not insert PDF', true); }
    finally { busy(false); }
  }

  function addBlankAfter() {
    const ref = pages[active];
    let w = 595.28, h = 841.89;
    if (ref) { const u = unrotatedSizePt(ref); w = u.w; h = u.h; }
    pages.splice(active + 1, 0, blankPage(w, h));
    active = active + 1;
    afterDocChange();
    toast('Blank page added');
  }

  function duplicatePage() {
    if (!pages.length) return;
    commitActiveAnn();
    const p = pages[active];
    const copy = Object.assign({}, p, {
      id: nextId(),
      annJSON: p.annJSON ? JSON.parse(JSON.stringify(p.annJSON)) : null,
      _hist: [], _hidx: -1, _imgEl: null, _proxy: p._proxy
    });
    pages.splice(active + 1, 0, copy);
    active = active + 1;
    afterDocChange();
    toast('Page duplicated');
  }

  function deletePage() {
    if (!pages.length) return;
    pages.splice(active, 1);
    if (active >= pages.length) active = pages.length - 1;
    afterDocChange();
    toast('Page deleted');
  }

  async function rotateActivePage() {
    if (!pages.length) return;
    if (viewMode !== 'single') await setViewMode('single');
    commitActiveAnn();
    const page = pages[active];
    if (fcanvas) {
      const ch = fcanvas.getHeight();
      fcanvas.getObjects().forEach(o => {
        const c = o.getCenterPoint();
        o.angle = (o.angle + 90) % 360;
        o.setPositionByOrigin(new fabric.Point(ch - c.y, c.x), 'center', 'center');
        o.setCoords();
      });
      page.annJSON = fcanvas.toJSON(FABRIC_PROPS);
    }
    page.rotation = (page.rotation + 90) % 360;
    page._hist = []; page._hidx = -1;
    await renderActive();
    invalidateThumb(page);
    toast('Page rotated');
  }

  async function extractSelected() {
    const idx = selectedIndices();
    if (!idx.length) { toast('Select pages first (checkboxes)', true); return; }
    commitActiveAnn();
    busy(true, 'Extracting\u2026');
    try {
      const bytes = await buildPdf(idx);
      saveBlob(new Blob([bytes], { type: 'application/pdf' }), 'extracted.pdf');
      toast(idx.length + ' page(s) extracted');
    } catch (e) { console.error(e); toast('Extract failed', true); }
    finally { busy(false); }
  }

  async function splitDocument(mode, n) {
    if (!pages.length) return;
    commitActiveAnn();
    busy(true, 'Splitting\u2026');
    try {
      const groups = [];
      if (mode === 'single') {
        for (let i = 0; i < pages.length; i++) groups.push([i]);
      } else {
        const step = Math.max(1, n | 0);
        for (let i = 0; i < pages.length; i += step) {
          groups.push(Array.from({ length: Math.min(step, pages.length - i) }, (_, k) => i + k));
        }
      }
      const files = [];
      for (let g = 0; g < groups.length; g++) {
        const bytes = await buildPdf(groups[g]);
        files.push({ name: 'part-' + String(g + 1).padStart(2, '0') + '.pdf', data: bytes });
      }
      const zip = createZip(files);
      saveBlob(new Blob([zip], { type: 'application/zip' }), 'split.zip');
      toast(files.length + ' file(s) zipped');
    } catch (e) { console.error(e); toast('Split failed', true); }
    finally { busy(false); }
  }

  async function downloadCurrent() {
    if (!pages.length) { toast('Nothing to export', true); return; }
    commitActiveAnn();
    busy(true, 'Building PDF\u2026');
    try {
      const bytes = await buildPdf(pages.map((_, i) => i));
      saveBlob(new Blob([bytes], { type: 'application/pdf' }), 'document.pdf');
      toast('PDF downloaded');
    } catch (e) { console.error(e); toast('Export failed', true); }
    finally { busy(false); }
  }

  // Called after any structural change to the page list.
  function afterDocChange() {
    rebuildThumbs();
    highlightThumb();
    updateChrome();
    updatePageStatus();
    if (!pages.length) { if (fcanvas) fcanvas.clear(); return; }
    if (viewMode === 'single') renderActive(); else buildContinuous();
  }

  /* ------------------------------ Annotations ---------------------------- */
  function placeImageAnnotation(file) {
    if (!file || !fcanvas) return;
    const reader = new FileReader();
    reader.onload = () => {
      fabric.Image.fromURL(reader.result, (img) => {
        const maxW = fcanvas.getWidth() * 0.6, maxH = fcanvas.getHeight() * 0.6;
        const s = Math.min(maxW / img.width, maxH / img.height, 1);
        img.set({ left: fcanvas.getWidth() / 2, top: fcanvas.getHeight() / 2, originX: 'center', originY: 'center', scaleX: s, scaleY: s });
        fcanvas.add(img); fcanvas.setActiveObject(img);
        setTool('select'); pushHistory();
      }, { crossOrigin: 'anonymous' });
    };
    reader.readAsDataURL(file);
  }

  function deleteActiveObject() {
    if (!fcanvas) return;
    const objs = fcanvas.getActiveObjects();
    if (!objs.length) return;
    objs.forEach(o => fcanvas.remove(o));
    fcanvas.discardActiveObject();
    fcanvas.requestRenderAll();
    pushHistory();
  }

  /* ----------------------------- Signature pad --------------------------- */
  function initSignaturePad() {
    const pad = $('signPad'), ctx = pad.getContext('2d');
    let drawing = false, last = null;
    const pos = (e) => {
      const r = pad.getBoundingClientRect();
      const cx = (e.touches ? e.touches[0].clientX : e.clientX) - r.left;
      const cy = (e.touches ? e.touches[0].clientY : e.clientY) - r.top;
      return { x: cx * (pad.width / r.width), y: cy * (pad.height / r.height) };
    };
    const start = (e) => { drawing = true; last = pos(e); e.preventDefault(); };
    const move = (e) => {
      if (!drawing) return;
      const p = pos(e);
      ctx.strokeStyle = $('signColor').value;
      ctx.lineWidth = 3; ctx.lineCap = 'round'; ctx.lineJoin = 'round';
      ctx.beginPath(); ctx.moveTo(last.x, last.y); ctx.lineTo(p.x, p.y); ctx.stroke();
      last = p; e.preventDefault();
    };
    const end = () => { drawing = false; };
    pad.addEventListener('mousedown', start); pad.addEventListener('mousemove', move);
    window.addEventListener('mouseup', end);
    pad.addEventListener('touchstart', start, { passive: false });
    pad.addEventListener('touchmove', move, { passive: false });
    pad.addEventListener('touchend', end);
    $('signClear').addEventListener('click', () => ctx.clearRect(0, 0, pad.width, pad.height));
  }

  function isPadEmpty() {
    const pad = $('signPad');
    const d = pad.getContext('2d').getImageData(0, 0, pad.width, pad.height).data;
    for (let i = 3; i < d.length; i += 4) if (d[i] !== 0) return false;
    return true;
  }

  function addSignatureToPage() {
    if (isPadEmpty()) { toast('Draw a signature first', true); return; }
    if (!fcanvas) { $('dlgSign').close(); return; }
    const url = $('signPad').toDataURL('image/png');
    fabric.Image.fromURL(url, (img) => {
      const w = fcanvas.getWidth() * 0.32, s = w / img.width;
      img.set({ left: fcanvas.getWidth() / 2, top: fcanvas.getHeight() / 2, originX: 'center', originY: 'center', scaleX: s, scaleY: s });
      fcanvas.add(img); fcanvas.setActiveObject(img);
      setTool('select'); pushHistory();
    });
    $('dlgSign').close();
  }

  /* ------------------------------- Zooming ------------------------------- */
  function setZoom(pct) {
    fitMode = null;
    zoomPct = clamp(pct, ZOOM_MIN, ZOOM_MAX);
    if (viewMode === 'single') applyZoom(); else zoomContinuous();
  }
  const zoomIn = () => setZoom(zoomPct + (zoomPct < 100 ? 10 : 25));
  const zoomOut = () => setZoom(zoomPct - (zoomPct <= 100 ? 10 : 25));
  function fit(mode) {
    if (!pages.length) return;
    if (viewMode !== 'single') setViewMode('single');
    fitMode = mode; recomputeFit();
  }

  /* -------------------------------- Theme -------------------------------- */
  function applyTheme(theme) {
    document.documentElement.setAttribute('data-theme', theme);
    try { localStorage.setItem('pdfstudio-theme', theme); } catch (e) {}
  }
  function toggleTheme() {
    const cur = document.documentElement.getAttribute('data-theme');
    applyTheme(cur === 'dark' ? 'light' : 'dark');
  }
  (function initTheme() {
    let t = 'light';
    try { t = localStorage.getItem('pdfstudio-theme') || 'light'; } catch (e) {}
    document.documentElement.setAttribute('data-theme', t);
  })();

  /* -------------------------------- Dialogs ------------------------------ */
  function openNumbersDialog() {
    $('numFormat').value = numberCfg.format;
    $('numPos').value = numberCfg.pos;
    $('numSize').value = numberCfg.size;
    $('numStart').value = numberCfg.start;
    $('numColor').value = numberCfg.color;
    $('numEnabled').checked = numberCfg.enabled;
    $('dlgNumbers').showModal();
  }

  /* ----------------------------- Event wiring ---------------------------- */
  function pick(inputId) { $(inputId).value = ''; $(inputId).click(); }

  function wireUI() {
    // File group
    $('btnOpen').addEventListener('click', () => pick('fileOpen'));
    $('emptyOpen').addEventListener('click', () => pick('fileOpen'));
    $('btnImages').addEventListener('click', () => pick('fileImages'));
    $('emptyImages').addEventListener('click', () => pick('fileImages'));
    $('btnSave').addEventListener('click', downloadCurrent);
    $('btnNew').addEventListener('click', () => $('dlgNew').showModal());
    $('emptyNew').addEventListener('click', () => $('dlgNew').showModal());

    $('fileOpen').addEventListener('change', (e) => { if (e.target.files.length) openFiles(e.target.files, { merge: pages.length > 0 }); });
    $('fileImages').addEventListener('change', (e) => { if (e.target.files.length) addImagesAsPages(e.target.files); });
    $('fileImage').addEventListener('change', (e) => { if (e.target.files[0]) placeImageAnnotation(e.target.files[0]); });
    $('fileInsert').addEventListener('change', (e) => { if (e.target.files[0]) insertFromFile(e.target.files[0]); });

    // Pages group
    $('btnAddPage').addEventListener('click', addBlankAfter);
    $('btnDuplicate').addEventListener('click', duplicatePage);
    $('btnRotate').addEventListener('click', rotateActivePage);
    $('btnDeletePage').addEventListener('click', deletePage);
    $('btnInsert').addEventListener('click', () => pick('fileInsert'));
    $('btnExtract').addEventListener('click', extractSelected);
    $('btnSplit').addEventListener('click', () => $('dlgSplit').showModal());
    $('btnNumbers').addEventListener('click', openNumbersDialog);

    // Tools
    document.querySelectorAll('.tbtn.tool').forEach(b => b.addEventListener('click', () => setTool(b.dataset.tool)));
    $('btnAddImage').addEventListener('click', () => { if (pages.length) pick('fileImage'); else toast('Open a document first', true); });
    $('btnSign').addEventListener('click', () => { if (!pages.length) return toast('Open a document first', true); $('dlgSign').showModal(); });
    $('btnUndo').addEventListener('click', undo);
    $('btnRedo').addEventListener('click', redo);
    $('btnDeleteObj').addEventListener('click', deleteActiveObject);

    inColor.addEventListener('input', () => {
      if (fcanvas && fcanvas.freeDrawingBrush) fcanvas.freeDrawingBrush.color = inColor.value;
      const o = fcanvas && fcanvas.getActiveObject();
      if (o) { applyStyleToObj(o, inColor.value, null); fcanvas.requestRenderAll(); pushHistory(); }
    });
    inThick.addEventListener('input', () => {
      if (fcanvas && fcanvas.freeDrawingBrush) fcanvas.freeDrawingBrush.width = +inThick.value;
      const o = fcanvas && fcanvas.getActiveObject();
      if (o) { applyStyleToObj(o, null, +inThick.value); fcanvas.requestRenderAll(); }
    });

    // View group
    $('btnViewToggle').addEventListener('click', () => setViewMode(viewMode === 'single' ? 'continuous' : 'single'));
    $('btnZoomIn').addEventListener('click', zoomIn);
    $('btnZoomOut').addEventListener('click', zoomOut);
    $('btnFitWidth').addEventListener('click', () => fit('width'));
    $('btnFitPage').addEventListener('click', () => fit('page'));
    $('btnTheme').addEventListener('click', toggleTheme);
    $('btnHelp').addEventListener('click', () => $('dlgHelp').showModal());

    // Select-all
    selAll.addEventListener('change', () => {
      [...thumbs.querySelectorAll('.pick')].forEach(b => { b.checked = selAll.checked; });
      selAll.indeterminate = false;
    });

    // Dialog: new
    $('dlgNew').addEventListener('close', () => {
      if ($('dlgNew').returnValue === 'ok') doNewBlank($('newSize').value, $('newOrient').value);
    });
    // Dialog: split
    $('dlgSplit').addEventListener('close', () => {
      if ($('dlgSplit').returnValue !== 'ok') return;
      const mode = document.querySelector('input[name="splitMode"]:checked').value;
      splitDocument(mode, +$('splitN').value);
    });
    // Dialog: numbers
    $('dlgNumbers').addEventListener('close', () => {
      if ($('dlgNumbers').returnValue !== 'ok') return;
      numberCfg = {
        enabled: $('numEnabled').checked,
        format: $('numFormat').value,
        pos: $('numPos').value,
        size: clamp(+$('numSize').value, 6, 48),
        start: Math.max(1, +$('numStart').value || 1),
        color: $('numColor').value
      };
      toast(numberCfg.enabled ? 'Page numbers will be added on export' : 'Page numbers disabled');
    });
    // Dialog: signature
    $('signCancel').addEventListener('click', () => $('dlgSign').close());
    $('signAdd').addEventListener('click', addSignatureToPage);

    // Drag & drop
    let dragDepth = 0;
    const overlay = $('dropOverlay');
    window.addEventListener('dragenter', (e) => { e.preventDefault(); if (hasFiles(e)) { dragDepth++; overlay.hidden = false; } });
    window.addEventListener('dragover', (e) => e.preventDefault());
    window.addEventListener('dragleave', (e) => { e.preventDefault(); if (--dragDepth <= 0) { dragDepth = 0; overlay.hidden = true; } });
    window.addEventListener('drop', (e) => {
      e.preventDefault(); dragDepth = 0; overlay.hidden = true;
      const files = [...(e.dataTransfer ? e.dataTransfer.files : [])];
      const pdfs = files.filter(f => f.type === 'application/pdf' || /\.pdf$/i.test(f.name));
      const imgs = files.filter(f => /^image\/(png|jpeg|webp)$/.test(f.type));
      if (pdfs.length) openFiles(pdfs, { merge: pages.length > 0 });
      else if (imgs.length) addImagesAsPages(imgs);
    });

    // Keyboard shortcuts
    window.addEventListener('keydown', onKey);

    // Re-fit on resize
    let rt = null;
    window.addEventListener('resize', () => { clearTimeout(rt); rt = setTimeout(() => { if (fitMode) recomputeFit(); }, 120); });
  }

  function hasFiles(e) {
    return e.dataTransfer && [...(e.dataTransfer.types || [])].includes('Files');
  }

  function isTyping() {
    const a = document.activeElement;
    if (!a) return false;
    const tag = a.tagName;
    if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT' || a.isContentEditable) return true;
    if (fcanvas) { const o = fcanvas.getActiveObject(); if (o && o.isEditing) return true; }
    return false;
  }

  function onKey(e) {
    if (document.querySelector('dialog[open]')) return;
    const meta = e.ctrlKey || e.metaKey;
    if (meta) {
      const k = e.key.toLowerCase();
      if (k === 'o') { e.preventDefault(); pick('fileOpen'); return; }
      if (k === 'n') { e.preventDefault(); $('dlgNew').showModal(); return; }
      if (k === 's') { e.preventDefault(); downloadCurrent(); return; }
      if (k === 'z') { e.preventDefault(); e.shiftKey ? redo() : undo(); return; }
      if (k === 'y') { e.preventDefault(); redo(); return; }
      if (e.key === '=' || e.key === '+') { e.preventDefault(); zoomIn(); return; }
      if (e.key === '-' || e.key === '_') { e.preventDefault(); zoomOut(); return; }
      return;
    }
    if (isTyping()) return;
    if (e.key === 'ArrowLeft') { if (active > 0) setActive(active - 1); }
    else if (e.key === 'ArrowRight') { if (active < pages.length - 1) setActive(active + 1); }
    else if (e.key === 'Delete' || e.key === 'Backspace') {
      if (fcanvas && fcanvas.getActiveObject()) { e.preventDefault(); deleteActiveObject(); }
    }
    else if (e.key === 'v' || e.key === 'V') setTool('select');
    else if (e.key === 't' || e.key === 'T') setTool('text');
    else if (e.key === 'd' || e.key === 'D') setTool('draw');
    else if (e.key === 'r' || e.key === 'R') rotateActivePage();
  }

  /* ----------------------------- Service worker -------------------------- */
  function registerSW() {
    if (!('serviceWorker' in navigator)) return;
    window.addEventListener('load', () => {
      navigator.serviceWorker.register('sw.js').then(() => {
        statusOffline.hidden = false;
      }).catch(() => { /* offline support simply unavailable */ });
    });
  }

  /* --------------------------------- Init -------------------------------- */
  function init() {
    if (!ENCRYPT_SUPPORTED) {
      // Gracefully disable the unavailable security feature without faking it.
      const btn = document.getElementById('btnLock');
      if (btn) { btn.disabled = true; btn.title = 'Password protection unavailable in this build'; }
    }
    wireUI();
    initSignaturePad();
    setTool('select');
    updateChrome();
    updatePageStatus();
    updateUndoRedo();
    updateObjButtons();
    registerSW();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
