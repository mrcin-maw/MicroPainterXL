'use strict';

// ── Constants ────────────────────────────────────────────────────────────────
const WIDTH    = 160;
const HEIGHT   = 200;
const CHUNK_W  = 4;
const CHUNK_H  = 8;
const CHUNKS_X = WIDTH  / CHUNK_W;   // 40
const CHUNKS_Y = HEIGHT / CHUNK_H;   // 25

const PAL_COLS  = 16;
const PAL_ROWS  = 16;
const PAL_TOTAL = PAL_COLS * PAL_ROWS;   // 256
const PALCELL   = 16;   // cell size in palette picker canvas (px)

const STORAGE_KEY    = 'micropxl-v3';
const STATE_VERSION  = 3;

const DEFAULT_GLOBAL_PAL = [0, 18, 40, 70, 100];  // palette indices (0-255)
const COLOR_NAMES = ['BAK', 'COL1', 'COL2', 'COL3', 'COL4'];

// Grid colours
const GRID_FINE  = '#2a2a2a';
const GRID_CHUNK = '#4a4a4a';

// ── DOM refs ──────────────────────────────────────────────────────────────────
const mainCanvas     = document.getElementById('mainCanvas');
const previewCanvas  = document.getElementById('previewCanvas');
const canvasOuter    = document.getElementById('canvasOuter');
const canvasWrap     = document.getElementById('canvasWrap');
const rowLabels      = document.getElementById('rowLabels');
const colorBtnsWrap  = document.getElementById('colorBtnsWrap');
const statusEl       = document.getElementById('statusEl');
const rowPopup       = document.getElementById('rowPopup');
const rowPopupTitle  = document.getElementById('rowPopupTitle');
const rowPopupColors = document.getElementById('rowPopupColors');
const palPicker      = document.getElementById('palPicker');
const palPickerTitle = document.getElementById('palPickerTitle');
const palCanvas      = document.getElementById('palCanvas');
const palHoverInfo   = document.getElementById('palHoverInfo');
const palResetBtn    = document.getElementById('palResetBtn');

const ctx        = mainCanvas.getContext('2d');
const previewCtx = previewCanvas.getContext('2d');
const palCtx     = palCanvas.getContext('2d');

// Offscreen buffer: 320×200 (no grid) for PNG export and preview
const offscreen  = document.createElement('canvas');
offscreen.width  = WIDTH * 2;
offscreen.height = HEIGHT;
const offCtx     = offscreen.getContext('2d');

// ── State ─────────────────────────────────────────────────────────────────────
let zoom       = 2;
let showGrid   = true;
let activeSlot = 1;    // 0=BAK … 4=COL4
let drawing    = false;
let cachedRect = null;

let palette256   = buildGrayscalePalette();   // 256 RGB entries
let globalPalette  = [...DEFAULT_GLOBAL_PAL];   // 5 palette indices
// rowOverrides[r][s] = null → use globalPalette[s], or a palette index
let rowOverrides = Array.from({ length: CHUNKS_Y }, () => Array(5).fill(null));
let pixels       = new Uint8Array(WIDTH * HEIGHT);
let saveTimer    = null;

// Popup state
let openRowIdx  = -1;
let pickingRow  = -2;   // -2=none, -1=global, 0..24=row
let pickingSlot = -1;

// ── Utilities ─────────────────────────────────────────────────────────────────
function buildGrayscalePalette() {
  return Array.from({ length: 256 }, (_, i) => {
    const g = Math.round(i * 255 / 255);
    return [g, g, g];
  });
}

function setStatus(msg) { statusEl.textContent = msg; }

function hex2(v) { return (v & 0xff).toString(16).toUpperCase().padStart(2, '0'); }

function rgbToHex(rgb) {
  if (!rgb) return '#000000';
  return '#' + hex2(rgb[0]) + hex2(rgb[1]) + hex2(rgb[2]);
}

function luma(rgb) { return 0.299 * rgb[0] + 0.587 * rgb[1] + 0.114 * rgb[2]; }

function clamp(n, lo, hi) { return Math.max(lo, Math.min(hi, n)); }

// ── Palette model ─────────────────────────────────────────────────────────────
function getEffectivePalette(rowIdx) {
  const ov = rowOverrides[rowIdx];
  return [0,1,2,3,4].map(s => ov[s] !== null ? ov[s] : globalPalette[s]);
}

function hasRowOverride(rowIdx) {
  return rowOverrides[rowIdx].some(v => v !== null);
}

// ── Pixel helpers ─────────────────────────────────────────────────────────────
function getChunkRow(y)  { return Math.floor(y / CHUNK_H); }
function getPixel(x, y)  { return pixels[y * WIDTH + x]; }
function setPixel(x, y, s) { pixels[y * WIDTH + x] = s; }

function chunkBounds(cx, cy) {
  return { x0: cx * CHUNK_W, y0: cy * CHUNK_H,
           x1: (cx + 1) * CHUNK_W, y1: (cy + 1) * CHUNK_H };
}

function applyCol3Col4Rule(cx, cy, slot) {
  if (slot !== 3 && slot !== 4) return;
  const { x0, y0, x1, y1 } = chunkBounds(cx, cy);
  const from = slot === 4 ? 3 : 4;
  for (let y = y0; y < y1; y++)
    for (let x = x0; x < x1; x++)
      if (getPixel(x, y) === from) setPixel(x, y, slot);
}

function chunkUsesCol4(cx, cy) {
  const { x0, y0, x1, y1 } = chunkBounds(cx, cy);
  for (let y = y0; y < y1; y++)
    for (let x = x0; x < x1; x++)
      if (getPixel(x, y) === 4) return true;
  return false;
}

// ── Palette loading ───────────────────────────────────────────────────────────
/**
 * Parse .pal / .act binary file → 256 RGB entries.
 * 768-byte files: 256 entries, read directly.
 * 384-byte files: 128 entries, expand to 256 (odd[i] = copy of even[i-1]).
 */
function parsePalBinary(data) {
  if (data.length >= 768) {
    return Array.from({ length: 256 }, (_, i) =>
      [data[i * 3], data[i * 3 + 1], data[i * 3 + 2]]);
  }
  if (data.length >= 384) {
    const base = Array.from({ length: 128 }, (_, i) =>
      [data[i * 3], data[i * 3 + 1], data[i * 3 + 2]]);
    return Array.from({ length: 256 }, (_, i) => [...base[Math.floor(i / 2)]]);
  }
  throw new Error('Plik palety za krótki (' + data.length + ' B, wymagane ≥ 384 B).');
}

async function loadPaletteFromFile(file) {
  const buf  = await file.arrayBuffer();
  const data = new Uint8Array(buf);
  const name = file.name.toLowerCase();
  if (name.endsWith('.pal') || name.endsWith('.act')) return parsePalBinary(data);
  return JSON.parse(new TextDecoder().decode(data))
    .slice(0, 256)
    .map(c => Array.isArray(c) ? c : [c.r, c.g, c.b]);
}

async function loadDefaultPalette() {
  const res = await fetch('./palettes/altirrapal.pal');
  if (!res.ok) throw new Error('HTTP ' + res.status);
  palette256 = parsePalBinary(new Uint8Array(await res.arrayBuffer()));
}

// ── Export / import ───────────────────────────────────────────────────────────
function slotFrom2bit(v2, col4flag) { return v2 <= 2 ? v2 : (col4flag ? 4 : 3); }
function bit2FromSlot(s)            { return s <= 2 ? s : 3; }

function encodeByteFrom4Pixels(xStart, y) {
  let v = 0;
  for (let i = 0; i < 4; i++) v = (v << 2) | bit2FromSlot(getPixel(xStart + i, y));
  return v;
}

function decodeByteTo4Pixels(byte, xStart, y, col4flag) {
  for (let i = 3; i >= 0; i--) {
    setPixel(xStart + i, y, slotFrom2bit(byte & 0b11, col4flag));
    byte >>= 2;
  }
}

function buildEffectiveTable3() {
  return Array.from({ length: HEIGHT }, (_, y) => [...getEffectivePalette(getChunkRow(y))]);
}

function parseHexByte(str) {
  if (typeof str === 'number') return str & 0xff;
  const n = parseInt(String(str).replace(/[$\s]/g, ''), 16);
  if (isNaN(n)) throw new Error('Nieprawidłowy bajt: ' + str);
  return n & 0xff;
}

function makeLinearExportObject() {
  const table1 = Array.from({ length: HEIGHT }, (_, y) =>
    Array.from({ length: CHUNKS_X }, (__, cx) => '$' + hex2(encodeByteFrom4Pixels(cx * 4, y))));
  const table2 = Array.from({ length: CHUNKS_Y }, (_, cy) =>
    Array.from({ length: CHUNKS_X }, (__, cx) => chunkUsesCol4(cx, cy) ? '$80' : '$00'));
  return {
    format: 'linear-v1', width: WIDTH, height: HEIGHT,
    chunkSize: { w: CHUNK_W, h: CHUNK_H },
    table1, table2, table3: buildEffectiveTable3(),
    globalPalette: [...globalPalette],
    rowOverrides: rowOverrides.map(r => [...r])
  };
}

function makeCharExportObject() {
  const groups = Math.ceil(CHUNKS_Y / 3);
  const blocks = Array.from({ length: groups }, (_, g) => {
    const bytes = [];
    for (let lr = 0; lr < 3; lr++) {
      const cy = g * 3 + lr;
      const valid = cy < CHUNKS_Y;
      for (let cx = 0; cx < CHUNKS_X; cx++)
        for (let ly = 0; ly < CHUNK_H; ly++)
          bytes.push(valid ? '$' + hex2(encodeByteFrom4Pixels(cx * 4, cy * CHUNK_H + ly)) : '$00');
    }
    return bytes;
  });
  const table2 = Array.from({ length: CHUNKS_Y }, (_, cy) =>
    Array.from({ length: CHUNKS_X }, (__, cx) => chunkUsesCol4(cx, cy) ? '$80' : '$00'));
  return {
    format: 'char-v1', width: WIDTH, height: HEIGHT,
    chunkSize: { w: CHUNK_W, h: CHUNK_H },
    table1Blocks: blocks, table2, table3: buildEffectiveTable3(),
    globalPalette: [...globalPalette],
    rowOverrides: rowOverrides.map(r => [...r])
  };
}

function importLinear(obj) {
  if (!Array.isArray(obj.table1) || obj.table1.length !== HEIGHT) throw new Error('Błędna table1.');
  if (!Array.isArray(obj.table2) || obj.table2.length !== CHUNKS_Y) throw new Error('Błędna table2.');
  pixels = new Uint8Array(WIDTH * HEIGHT);
  for (let y = 0; y < HEIGHT; y++) {
    const cy = getChunkRow(y);
    for (let cx = 0; cx < CHUNKS_X; cx++) {
      const f4 = parseHexByte(obj.table2[cy][cx]) === 0x80;
      decodeByteTo4Pixels(parseHexByte(obj.table1[y][cx]), cx * 4, y, f4);
    }
  }
  applyImportedPalette(obj);
}

function importChar(obj) {
  if (!Array.isArray(obj.table1Blocks)) throw new Error('Brak table1Blocks.');
  if (!Array.isArray(obj.table2) || obj.table2.length !== CHUNKS_Y) throw new Error('Błędna table2.');
  pixels = new Uint8Array(WIDTH * HEIGHT);
  const groups = Math.ceil(CHUNKS_Y / 3);
  for (let g = 0; g < groups; g++) {
    const block = obj.table1Blocks[g];
    if (!Array.isArray(block)) throw new Error('Brak bloku ' + g + '.');
    let p = 0;
    for (let lr = 0; lr < 3; lr++) {
      const cy = g * 3 + lr;
      const valid = cy < CHUNKS_Y;
      for (let cx = 0; cx < CHUNKS_X; cx++) {
        const f4 = valid ? parseHexByte(obj.table2[cy][cx]) === 0x80 : false;
        for (let ly = 0; ly < CHUNK_H; ly++) {
          const raw  = block[p++];
          const byte = parseHexByte(raw !== undefined ? raw : '$00');
          if (valid) decodeByteTo4Pixels(byte, cx * 4, cy * CHUNK_H + ly, f4);
        }
      }
    }
  }
  applyImportedPalette(obj);
}

function applyImportedPalette(obj) {
  // New format: globalPalette + rowOverrides
  if (Array.isArray(obj.globalPalette) && obj.globalPalette.length >= 5) {
    globalPalette = obj.globalPalette.slice(0, 5).map(v => clamp(Number(v) || 0, 0, 255));
  }
  if (Array.isArray(obj.rowOverrides) && obj.rowOverrides.length === CHUNKS_Y) {
    rowOverrides = obj.rowOverrides.map(r =>
      Array.isArray(r) && r.length >= 5
        ? r.slice(0, 5).map(v => v === null ? null : clamp(Number(v) || 0, 0, 255))
        : Array(5).fill(null));
    return;
  }
  // Backward compat: old table3 → treat as row overrides (all set)
  if (Array.isArray(obj.table3) && obj.table3.length >= HEIGHT) {
    rowOverrides = Array.from({ length: CHUNKS_Y }, () => Array(5).fill(null));
    const seenRow = new Set();
    for (let y = 0; y < HEIGHT; y++) {
      const r = getChunkRow(y);
      if (seenRow.has(r)) continue;
      seenRow.add(r);
      const v = obj.table3[y];
      if (Array.isArray(v) && v.length >= 5)
        rowOverrides[r] = v.slice(0, 5).map(n => clamp(Number(n) || 0, 0, 255));
    }
  }
}

// ── Persistence ───────────────────────────────────────────────────────────────
function scheduleSave() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(saveState, 400);
}

function saveState() {
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify({
      v: STATE_VERSION, pixels: Array.from(pixels),
      globalPalette, rowOverrides, palette256, zoom, showGrid
    }));
  } catch (_) {}
}

function restoreState() {
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (!raw) return false;
    const st = JSON.parse(raw);
    if (st.v !== STATE_VERSION) return false;  // discard old versions
    if (Array.isArray(st.palette256) && st.palette256.length === 256)
      palette256 = st.palette256;
    if (Array.isArray(st.globalPalette) && st.globalPalette.length >= 5)
      globalPalette = st.globalPalette.slice(0, 5).map(v => clamp(Number(v) || 0, 0, 255));
    if (Array.isArray(st.rowOverrides) && st.rowOverrides.length === CHUNKS_Y)
      rowOverrides = st.rowOverrides.map(r =>
        Array.isArray(r) ? r.slice(0, 5).map(v => v === null ? null : clamp(Number(v)||0,0,255)) : Array(5).fill(null));
    if (Array.isArray(st.pixels) && st.pixels.length === WIDTH * HEIGHT)
      pixels = Uint8Array.from(st.pixels.map(v => clamp(v, 0, 4)));
    if ([1, 2, 4, 8].includes(st.zoom)) zoom = st.zoom;
    if (typeof st.showGrid === 'boolean') showGrid = st.showGrid;
    return true;
  } catch (_) { return false; }
}

// ── Drawing ───────────────────────────────────────────────────────────────────
function cellW() { return 2 * zoom + 1; }  // canvas px per logical pixel (x)
function cellH() { return zoom + 1; }       // canvas px per logical pixel (y)
function canvasW() { return 1 + WIDTH  * cellW(); }
function canvasH() { return 1 + HEIGHT * cellH(); }

/**
 * Draw everything onto mainCanvas.
 * canvas DOM size = display CSS size (no zoom-scaling of canvas element).
 * Each logical pixel → 2Z×Z canvas pixels, separated by 1px grid lines.
 */
function renderCanvas() {
  const CW = cellW(), CH = cellH();
  const cW = canvasW(), cH = canvasH();

  if (mainCanvas.width !== cW || mainCanvas.height !== cH) {
    mainCanvas.width  = cW;
    mainCanvas.height = cH;
  }

  // Fill with fine grid colour
  ctx.fillStyle = GRID_FINE;
  ctx.fillRect(0, 0, cW, cH);

  // Chunk boundaries (brighter)
  if (showGrid) {
    ctx.fillStyle = GRID_CHUNK;
    for (let cx = 0; cx <= CHUNKS_X; cx++)
      ctx.fillRect(cx * CHUNK_W * CW, 0, 1, cH);
    for (let cy = 0; cy <= CHUNKS_Y; cy++)
      ctx.fillRect(0, cy * CHUNK_H * CH, cW, 1);
  }

  // Draw pixels
  const pxW = 2 * zoom, pxH = zoom;
  for (let y = 0; y < HEIGHT; y++) {
    const eff = getEffectivePalette(getChunkRow(y));
    const cy  = 1 + y * CH;
    for (let x = 0; x < WIDTH; x++) {
      const col = palette256[eff[getPixel(x, y)]] || [0, 0, 0];
      ctx.fillStyle = 'rgb(' + col[0] + ',' + col[1] + ',' + col[2] + ')';
      ctx.fillRect(1 + x * CW, cy, pxW, pxH);
    }
  }
}

function renderOffscreen() {
  const img = offCtx.createImageData(WIDTH * 2, HEIGHT);
  const d   = img.data;
  for (let y = 0; y < HEIGHT; y++) {
    const eff = getEffectivePalette(getChunkRow(y));
    for (let x = 0; x < WIDTH; x++) {
      const col  = palette256[eff[getPixel(x, y)]] || [0, 0, 0];
      const base = (y * WIDTH * 2 + x * 2) * 4;
      d[base]     = d[base + 4]     = col[0];
      d[base + 1] = d[base + 5]     = col[1];
      d[base + 2] = d[base + 6]     = col[2];
      d[base + 3] = d[base + 7]     = 255;
    }
  }
  offCtx.putImageData(img, 0, 0);
}

function renderPreview(mouseX, mouseY) {
  previewCtx.imageSmoothingEnabled = false;
  previewCtx.clearRect(0, 0, previewCanvas.width, previewCanvas.height);
  previewCtx.drawImage(offscreen, 0, 0, previewCanvas.width, previewCanvas.height);
  updatePreviewPos(mouseX, mouseY);
}

function drawAll(mouseX, mouseY) {
  renderOffscreen();
  renderCanvas();
  renderPreview(mouseX, mouseY);
}

// ── Canvas positioning ─────────────────────────────────────────────────────────
function setCanvasSize() {
  // mainCanvas dimensions are set by renderCanvas()
  drawAll();
  refreshRowLabels();
  // Resize preview display proportionally (~1/8 of canvas)
  const pvW = Math.max(40, Math.round(canvasW() / 8));
  const pvH = Math.max(20, Math.round(canvasH() / 8));
  previewCanvas.style.width  = pvW + 'px';
  previewCanvas.style.height = pvH + 'px';
}

// ── Coordinate conversion ──────────────────────────────────────────────────────
function coordsFromEvent(e) {
  const rect = cachedRect || mainCanvas.getBoundingClientRect();
  const CW = cellW(), CH = cellH();
  // canvas CSS = canvas DOM (no CSS scaling), so device pixel ratio aside:
  const scaleX = mainCanvas.width  / rect.width;
  const scaleY = mainCanvas.height / rect.height;
  const domX = (e.clientX - rect.left) * scaleX;
  const domY = (e.clientY - rect.top)  * scaleY;
  const x = Math.floor((domX - 1) / CW);
  const y = Math.floor((domY - 1) / CH);
  if (x < 0 || y < 0 || x >= WIDTH || y >= HEIGHT) return null;
  return { x, y, cx: Math.floor(x / CHUNK_W), cy: Math.floor(y / CHUNK_H) };
}

function paintAtEvent(e) {
  const pos = coordsFromEvent(e);
  if (!pos) return;
  applyCol3Col4Rule(pos.cx, pos.cy, activeSlot);
  setPixel(pos.x, pos.y, activeSlot);
  renderOffscreen();
  renderCanvas();
  renderPreview(e.clientX, e.clientY);
  scheduleSave();
}

// ── Preview positioning ───────────────────────────────────────────────────────
function updatePreviewPos(clientX, clientY) {
  if (clientX === undefined) return;
  const rect    = mainCanvas.getBoundingClientRect();
  const inRight  = clientX - rect.left >= rect.width  / 2;
  const inBottom = clientY - rect.top  >= rect.height / 2;
  previewCanvas.style.right  = inRight  ? '4px' : 'auto';
  previewCanvas.style.left   = inRight  ? 'auto' : '4px';
  previewCanvas.style.bottom = inBottom ? '4px' : 'auto';
  previewCanvas.style.top    = inBottom ? 'auto' : '4px';
}

// ── Colour buttons (toolbar) ──────────────────────────────────────────────────
function refreshColorButtons() {
  colorBtnsWrap.innerHTML = '';
  COLOR_NAMES.forEach((name, slot) => {
    const col = palette256[globalPalette[slot]] || [0, 0, 0];
    const btn = document.createElement('button');
    btn.className = 'color-btn';
    btn.textContent = name;
    btn.style.background = rgbToHex(col);
    btn.style.color = luma(col) > 110 ? '#000' : '#fff';
    btn.style.textShadow = luma(col) > 110
      ? '0 0 2px rgba(255,255,255,0.4)' : '0 0 2px rgba(0,0,0,0.9)';
    if (slot === activeSlot) btn.classList.add('active');
    if ((activeSlot === 3 && slot === 4) || (activeSlot === 4 && slot === 3))
      btn.classList.add('dimmed');
    btn.addEventListener('pointerdown', ev => {
      ev.stopPropagation();
      if (activeSlot === slot) {
        // Already active → open global palette picker
        openPalettePicker(-1, slot, btn);
      } else {
        activeSlot = slot;
        refreshColorButtons();
      }
    });
    colorBtnsWrap.appendChild(btn);
  });
}

// ── Row labels (right-hand strip, attached to canvas rows) ────────────────────
function rowLabelHeight() { return CHUNK_H * cellH(); }   // CSS px per chunk row

function refreshRowLabels() {
  rowLabels.innerHTML = '';

  // 1px spacer for the leading canvas grid line
  const spacer = document.createElement('div');
  spacer.style.height = '1px';
  spacer.style.flexShrink = '0';
  rowLabels.appendChild(spacer);

  const rh = rowLabelHeight();
  for (let r = 0; r < CHUNKS_Y; r++) {
    const eff = getEffectivePalette(r);
    const div = document.createElement('div');
    div.className = 'row-lbl' + (hasRowOverride(r) ? ' has-override' : '');
    div.style.height = rh + 'px';
    div.dataset.row  = r;

    const num = document.createElement('span');
    num.className = 'row-lbl-num';
    num.textContent = r;
    div.appendChild(num);

    const sw = document.createElement('div');
    sw.className = 'row-swatches';
    for (let s = 0; s < 5; s++) {
      const sq = document.createElement('div');
      sq.className = 'row-swatch';
      sq.style.background = rgbToHex(palette256[eff[s]] || [0, 0, 0]);
      if (rowOverrides[r][s] !== null) sq.classList.add('swatch-overridden');
      sw.appendChild(sq);
    }
    div.appendChild(sw);

    div.addEventListener('click', ev => { ev.stopPropagation(); openRowPopup(r, div); });
    rowLabels.appendChild(div);
  }
}

// ── Row colour popup ──────────────────────────────────────────────────────────
function openRowPopup(rowIdx, anchorEl) {
  openRowIdx = rowIdx;
  rowPopupTitle.textContent =
    'Wiersz ' + rowIdx + '  (L' + rowIdx * CHUNK_H + '–' + (rowIdx * CHUNK_H + CHUNK_H - 1) + ')';
  rebuildRowPopupColors(rowIdx);
  rowPopup.hidden = false;
  positionNear(rowPopup, anchorEl, 'left');
}

function rebuildRowPopupColors(rowIdx) {
  const eff = getEffectivePalette(rowIdx);
  rowPopupColors.innerHTML = '';
  COLOR_NAMES.forEach((name, slot) => {
    const colIdx = eff[slot];
    const col    = palette256[colIdx] || [0, 0, 0];
    const isOvr  = rowOverrides[rowIdx][slot] !== null;

    const div = document.createElement('div');
    div.className = 'row-color-swatch' + (isOvr ? ' swatch-is-overridden' : '');

    const box = document.createElement('div');
    box.className = 'swatch-box';
    box.style.background = rgbToHex(col);

    const lbl = document.createElement('span');
    lbl.className = 'swatch-label';
    lbl.textContent = name;

    const idx = document.createElement('span');
    idx.className = 'swatch-idx';
    idx.textContent = '#' + String(colIdx).padStart(3, '0') + (isOvr ? ' ★' : '');

    div.append(box, lbl, idx);
    div.addEventListener('click', ev => { ev.stopPropagation(); openPalettePicker(rowIdx, slot, div); });
    rowPopupColors.appendChild(div);
  });
}

function closeRowPopup() {
  rowPopup.hidden = true;
  openRowIdx = -1;
}

// ── Palette picker ────────────────────────────────────────────────────────────
function drawPaletteCanvas() {
  palCtx.clearRect(0, 0, palCanvas.width, palCanvas.height);
  for (let r = 0; r < PAL_ROWS; r++) {
    for (let c = 0; c < PAL_COLS; c++) {
      const col = palette256[r * PAL_COLS + c] || [0, 0, 0];
      palCtx.fillStyle = rgbToHex(col);
      palCtx.fillRect(c * PALCELL, r * PALCELL, PALCELL, PALCELL);
    }
  }
}

function openPalettePicker(rowIdx, slot, anchorEl) {
  pickingRow  = rowIdx;
  pickingSlot = slot;

  const curIdx = rowIdx === -1
    ? globalPalette[slot]
    : getEffectivePalette(rowIdx)[slot];

  const rowLabel = rowIdx === -1 ? 'Globalny' : 'Wiersz ' + rowIdx;
  palPickerTitle.textContent = rowLabel + ' › ' + COLOR_NAMES[slot] + '  (#' + curIdx + ')';

  // Show/hide reset button
  const canReset = rowIdx >= 0 && rowOverrides[rowIdx][slot] !== null;
  palResetBtn.hidden = !canReset;

  drawPaletteCanvas();
  palHoverInfo.textContent = '\u00a0';
  palPicker.hidden = false;
  positionNear(palPicker, anchorEl, 'below');
}

function closePalettePicker() {
  palPicker.hidden = true;
  pickingRow  = -2;
  pickingSlot = -1;
}

function paletteIndexFromEvent(e) {
  const rect = palCanvas.getBoundingClientRect();
  const px = (e.clientX - rect.left) * palCanvas.width  / rect.width;
  const py = (e.clientY - rect.top)  * palCanvas.height / rect.height;
  const c  = Math.floor(px / PALCELL);
  const r  = Math.floor(py / PALCELL);
  if (c < 0 || c >= PAL_COLS || r < 0 || r >= PAL_ROWS) return -1;
  return r * PAL_COLS + c;
}

function applyPickedColor(idx) {
  if (idx < 0 || pickingSlot < 0 || pickingRow < -1) return;
  if (pickingRow === -1) {
    // Global palette
    globalPalette[pickingSlot] = idx;
  } else {
    rowOverrides[pickingRow][pickingSlot] = idx;
  }
  afterColorPick();
}

function afterColorPick() {
  if (openRowIdx >= 0) rebuildRowPopupColors(openRowIdx);
  drawAll();
  refreshRowLabels();
  refreshColorButtons();
  scheduleSave();
  closePalettePicker();
}

function resetSlotToGlobal() {
  if (pickingRow < 0 || pickingSlot < 0) return;
  rowOverrides[pickingRow][pickingSlot] = null;
  afterColorPick();
}

// ── Popup positioning ─────────────────────────────────────────────────────────
function positionNear(popup, anchor, prefer) {
  popup.style.top  = '-9999px';
  popup.style.left = '-9999px';
  popup.style.bottom = 'auto';
  popup.style.right  = 'auto';

  const aR  = anchor.getBoundingClientRect();
  const pW  = popup.offsetWidth  || 240;
  const pH  = popup.offsetHeight || 240;
  const vW  = window.innerWidth;
  const vH  = window.innerHeight;
  const pad = 6;

  let left, top;
  if (prefer === 'left') {
    left = aR.left - pW - pad;
    if (left < pad) left = aR.right + pad;
    top  = clamp(aR.top, pad, vH - pH - pad);
  } else {
    top  = aR.bottom + pad;
    if (top + pH > vH - pad) top = aR.top - pH - pad;
    left = clamp(aR.left, pad, vW - pW - pad);
  }
  popup.style.left = Math.max(pad, left) + 'px';
  popup.style.top  = Math.max(pad, top)  + 'px';
}

// ── File helpers ──────────────────────────────────────────────────────────────
function downloadBlob(name, blob) {
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = name;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
}

function downloadJson(name, obj) {
  downloadBlob(name, new Blob([JSON.stringify(obj, null, 2)], { type: 'application/json' }));
}

function exportPng() {
  return new Promise((res, rej) =>
    offscreen.toBlob(blob => {
      if (!blob) { rej(new Error('toBlob zwróciło null.')); return; }
      downloadBlob('screen_320x200.png', blob);
      res();
    }, 'image/png'));
}

// ── Event binding ─────────────────────────────────────────────────────────────
function bindEvents() {
  // Zoom buttons
  document.querySelectorAll('[data-zoom]').forEach(btn => {
    btn.addEventListener('click', () => {
      zoom = Number(btn.dataset.zoom);
      document.querySelectorAll('[data-zoom]').forEach(b =>
        b.classList.toggle('active', Number(b.dataset.zoom) === zoom));
      setCanvasSize();
      scheduleSave();
    });
  });
  document.querySelectorAll('[data-zoom]').forEach(b =>
    b.classList.toggle('active', Number(b.dataset.zoom) === zoom));

  // Grid toggle
  const gridToggle = document.getElementById('gridToggle');
  gridToggle.checked = showGrid;
  gridToggle.addEventListener('change', () => {
    showGrid = gridToggle.checked;
    renderCanvas();
    scheduleSave();
  });

  // Drawing events on mainCanvas
  mainCanvas.addEventListener('pointerdown', e => {
    drawing    = true;
    cachedRect = mainCanvas.getBoundingClientRect();
    mainCanvas.setPointerCapture(e.pointerId);
    paintAtEvent(e);
  });
  mainCanvas.addEventListener('pointermove', e => {
    if (drawing) paintAtEvent(e);
    else updatePreviewPos(e.clientX, e.clientY);
  });
  mainCanvas.addEventListener('pointerup', e => {
    drawing    = false;
    cachedRect = null;
    mainCanvas.releasePointerCapture(e.pointerId);
  });
  mainCanvas.addEventListener('pointercancel', () => {
    drawing = false; cachedRect = null;
  });

  // Toolbar buttons
  document.getElementById('clearBtn').addEventListener('click', () => {
    pixels.fill(0); drawAll(); refreshRowLabels(); scheduleSave();
    setStatus('Ekran wyczyszczony.');
  });
  document.getElementById('exportLinearBtn').addEventListener('click', () => {
    downloadJson('screen_linear_v1.json', makeLinearExportObject());
    setStatus('Wyeksportowano JSON linear-v1.');
  });
  document.getElementById('exportCharBtn').addEventListener('click', () => {
    downloadJson('screen_char_v1.json', makeCharExportObject());
    setStatus('Wyeksportowano JSON char-v1.');
  });
  document.getElementById('exportPngBtn').addEventListener('click', async () => {
    try { await exportPng(); setStatus('Wyeksportowano PNG 320×200.'); }
    catch (ex) { setStatus('Błąd PNG: ' + ex.message); }
  });

  document.getElementById('importJsonInput').addEventListener('change', async ev => {
    const file = ev.target.files && ev.target.files[0];
    if (!file) return;
    try {
      const obj = JSON.parse(await file.text());
      if (obj.format === 'linear-v1') importLinear(obj);
      else if (obj.format === 'char-v1') importChar(obj);
      else throw new Error('Nieznany format: ' + obj.format);
      drawAll(); refreshRowLabels(); refreshColorButtons();
      scheduleSave();
      setStatus('Wczytano ' + obj.format + '.');
    } catch (ex) { setStatus('Błąd importu: ' + ex.message); }
    ev.target.value = '';
  });

  document.getElementById('importPaletteInput').addEventListener('change', async ev => {
    const file = ev.target.files && ev.target.files[0];
    if (!file) return;
    try {
      palette256 = await loadPaletteFromFile(file);
      drawAll(); refreshRowLabels(); refreshColorButtons();
      scheduleSave();
      setStatus('Wczytano paletę: ' + file.name);
    } catch (ex) { setStatus('Błąd palety: ' + ex.message); }
    ev.target.value = '';
  });

  // Palette picker canvas events
  palCanvas.addEventListener('pointermove', e => {
    const idx = paletteIndexFromEvent(e);
    if (idx >= 0) {
      const col = palette256[idx] || [0, 0, 0];
      palHoverInfo.textContent =
        '#' + String(idx).padStart(3, '0') +
        '  R' + String(idx).padStart(2,'0') + 'C' + String(idx % PAL_COLS).padStart(2,'0') +
        '  ' + rgbToHex(col);
    } else {
      palHoverInfo.textContent = '\u00a0';
    }
  });
  palCanvas.addEventListener('click', e => applyPickedColor(paletteIndexFromEvent(e)));

  palResetBtn.addEventListener('click', e => { e.stopPropagation(); resetSlotToGlobal(); });
  document.getElementById('palPickerClose').addEventListener('click', e => {
    e.stopPropagation(); closePalettePicker();
  });
  document.getElementById('rowPopupClose').addEventListener('click', e => {
    e.stopPropagation(); closePalettePicker(); closeRowPopup();
  });

  // Close popups on outside click
  document.addEventListener('pointerdown', e => {
    if (!palPicker.hidden && !palPicker.contains(e.target)) closePalettePicker();
    if (!rowPopup.hidden && !rowPopup.contains(e.target) &&
        !e.target.closest('.row-lbl')) closeRowPopup();
  }, true);

  // Resize
  const ro = typeof ResizeObserver !== 'undefined'
    ? new ResizeObserver(() => { cachedRect = null; })
    : null;
  if (ro) ro.observe(canvasOuter);
  window.addEventListener('resize', () => { cachedRect = null; });
  window.addEventListener('beforeunload', saveState);
}

// ── Init ──────────────────────────────────────────────────────────────────────
async function init() {
  try {
    await loadDefaultPalette();
  } catch (e) {
    console.warn('altirrapal.pal:', e.message);
    setStatus('Ostrzeżenie: brak pliku palety – używam szarości.');
  }

  const hadState = restoreState();

  setCanvasSize();    // draws canvas + resizes preview
  refreshColorButtons();
  bindEvents();
  document.getElementById('gridToggle').checked = showGrid;
  document.querySelectorAll('[data-zoom]').forEach(b =>
    b.classList.toggle('active', Number(b.dataset.zoom) === zoom));

  setStatus(hadState ? 'Przywrócono poprzedni stan.' : 'Gotowe.');
}

init().catch(e => {
  setStatus('Błąd inicjalizacji: ' + e.message);
  console.error(e);
});
