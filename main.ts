// Squeeze — lossless PNG re-encoder.
// Reads 1280x720 RGBA screenshots from /input/<id>/image.png (or
// MAKEFUN_INPUT_DIR), writes each one back losslessly in as few bytes as
// possible to /output/<id>/image.png (or MAKEFUN_OUTPUT_DIR).
// Plain JavaScript in a .ts file (Node 22 type stripping). Deterministic:
// no clock, no randomness, no environment-dependent choices. Node built-ins only.

import { readdirSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { inflateSync, deflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// DEFLATE tables (RFC 1951)
// ---------------------------------------------------------------------------

const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

const LEN_CODE = new Array(259).fill(0);
const LEN_EXT = new Array(259).fill(0);
for (let len = 3; len <= 258; len++) {
  let idx = 0;
  while (idx < 28 && LEN_BASE[idx + 1] <= len) idx++;
  LEN_CODE[len] = idx;
  LEN_EXT[len] = LEN_EXTRA[idx];
}
const DIST_CODE = new Array(32769).fill(0);
const DIST_EXT = new Array(32769).fill(0);
for (let d = 1; d <= 32768; d++) {
  let idx = 0;
  while (idx < 29 && DIST_BASE[idx + 1] <= d) idx++;
  DIST_CODE[d] = idx;
  DIST_EXT[d] = DIST_EXTRA[idx];
}

// Fixed Huffman code lengths (RFC 1951 section 3.2.6).
const FIXED_LIT_LENS = new Array(288);
for (let i = 0; i < 288; i++) FIXED_LIT_LENS[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;
const FIXED_DIST_LENS = new Array(30).fill(5);

// ---------------------------------------------------------------------------
// Checksums
// ---------------------------------------------------------------------------

const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
    t[n] = c >>> 0;
  }
  return t;
})();

function crc32(buf, start, end) {
  let c = 0xFFFFFFFF;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}

function adler32(buf) {
  let a = 1;
  let b = 0;
  const MOD = 65521;
  for (let i = 0; i < buf.length; i++) {
    a = (a + buf[i]) % MOD;
    b = (b + a) % MOD;
  }
  return ((b << 16) | a) >>> 0;
}

// ---------------------------------------------------------------------------
// Huffman code lengths and canonical codes
// ---------------------------------------------------------------------------

// Build Huffman code lengths from symbol frequencies, capped at maxBits.
// Deterministic: ties broken by symbol/insertion order. If any length
// exceeds the cap, halve all frequencies (min 1) and rebuild.
function huffmanLengths(freqs, maxBits) {
  const n = freqs.length;
  const lengths = new Array(n).fill(0);
  let used = 0;
  let only = -1;
  for (let i = 0; i < n; i++) if (freqs[i] > 0) { used++; only = i; }
  if (used === 0) return lengths;
  if (used === 1) { lengths[only] = 1; return lengths; }
  let cur = freqs.slice();
  for (;;) {
    const list = [];
    let seq = 0;
    for (let i = 0; i < n; i++) {
      if (cur[i] > 0) list.push({ f: cur[i], sym: i, left: null, right: null, seq: seq++ });
    }
    list.sort((a, b) => (a.f - b.f) || (a.seq - b.seq));
    let nextSeq = n;
    while (list.length > 1) {
      const a = list.shift();
      const b = list.shift();
      const c = { f: a.f + b.f, sym: -1, left: a, right: b, seq: nextSeq++ };
      let pos = 0;
      while (pos < list.length && ((list[pos].f < c.f) || (list[pos].f === c.f && list[pos].seq < c.seq))) pos++;
      list.splice(pos, 0, c);
    }
    const root = list[0];
    const stack = [[root, 0]];
    let maxLen = 0;
    while (stack.length > 0) {
      const pair = stack.pop();
      const node = pair[0];
      const d = pair[1];
      if (node.sym >= 0) {
        lengths[node.sym] = d;
        if (d > maxLen) maxLen = d;
      } else {
        stack.push([node.left, d + 1]);
        stack.push([node.right, d + 1]);
      }
    }
    if (maxLen <= maxBits) return lengths;
    for (let i = 0; i < n; i++) if (cur[i] > 0) cur[i] = Math.max(1, cur[i] >> 1);
    lengths.fill(0);
  }
}

// Canonical Huffman codes from code lengths (MSB-first codes, as values).
function canonicalCodes(lengths) {
  let maxLen = 0;
  for (const l of lengths) if (l > maxLen) maxLen = l;
  const blCount = new Array(maxLen + 1).fill(0);
  for (const l of lengths) if (l > 0) blCount[l]++;
  const nextCode = new Array(maxLen + 1).fill(0);
  let code = 0;
  for (let b = 1; b <= maxLen; b++) {
    code = (code + blCount[b - 1]) << 1;
    nextCode[b] = code;
  }
  const codes = new Array(lengths.length).fill(0);
  for (let i = 0; i < lengths.length; i++) {
    const l = lengths[i];
    if (l > 0) { codes[i] = nextCode[l]; nextCode[l]++; }
  }
  return codes;
}

// ---------------------------------------------------------------------------
// Bit writer (LSB-first accumulator; Huffman codes emitted MSB-first)
// ---------------------------------------------------------------------------

class BitWriter {
  constructor() {
    this.bytes = [];
    this.acc = 0;
    this.nbits = 0;
  }
  putBits(value, len) {
    this.acc |= (value & ((1 << len) - 1)) << this.nbits;
    this.nbits += len;
    while (this.nbits >= 8) {
      this.bytes.push(this.acc & 0xFF);
      this.acc >>>= 8;
      this.nbits -= 8;
    }
  }
  putCode(code, len) {
    let rev = 0;
    for (let i = 0; i < len; i++) rev = (rev << 1) | ((code >> i) & 1);
    this.putBits(rev, len);
  }
  finish() {
    if (this.nbits > 0) {
      this.bytes.push(this.acc & 0xFF);
      this.acc = 0;
      this.nbits = 0;
    }
    return Buffer.from(this.bytes);
  }
}

// ---------------------------------------------------------------------------
// PNG decode / encode
// ---------------------------------------------------------------------------

function paeth(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  if (pb <= pc) return b;
  return c;
}

// Decode a PNG into { width, height, rgba } (RGBA bytes, 8 bit/channel).
// Handles bit depth 8, colour types 0, 2, 4, 6, all five filter types.
function decodePng(buf) {
  let pos = 8;
  let width = 0;
  let height = 0;
  let colorType = 6;
  const idat = [];
  while (pos + 8 <= buf.length) {
    const len = buf.readUInt32BE(pos);
    const type = buf.toString('ascii', pos + 4, pos + 8);
    const data = buf.subarray(pos + 8, pos + 8 + len);
    if (type === 'IHDR') {
      width = data.readUInt32BE(0);
      height = data.readUInt32BE(4);
      colorType = data[9];
    } else if (type === 'IDAT') {
      idat.push(data);
    } else if (type === 'IEND') {
      break;
    }
    pos += 12 + len;
  }
  const raw = inflateSync(Buffer.concat(idat));
  const bpp = colorType === 6 ? 4 : colorType === 2 ? 3 : colorType === 4 ? 2 : 1;
  const stride = width * bpp;
  const rgba = Buffer.alloc(width * height * 4);
  let src = 0;
  let prev = Buffer.alloc(stride);
  for (let y = 0; y < height; y++) {
    const filter = raw[src++];
    const row = raw.subarray(src, src + stride);
    src += stride;
    const out = Buffer.alloc(stride);
    for (let i = 0; i < stride; i++) {
      const a = i >= bpp ? out[i - bpp] : 0;
      const b = prev[i];
      const c = i >= bpp ? prev[i - bpp] : 0;
      let pred = 0;
      if (filter === 1) pred = a;
      else if (filter === 2) pred = b;
      else if (filter === 3) pred = (a + b) >> 1;
      else if (filter === 4) pred = paeth(a, b, c);
      out[i] = (row[i] + pred) & 0xFF;
    }
    const dst = y * width * 4;
    if (colorType === 6) {
      out.copy(rgba, dst);
    } else if (colorType === 2) {
      for (let x = 0; x < width; x++) {
        rgba[dst + x * 4] = out[x * 3];
        rgba[dst + x * 4 + 1] = out[x * 3 + 1];
        rgba[dst + x * 4 + 2] = out[x * 3 + 2];
        rgba[dst + x * 4 + 3] = 255;
      }
    } else if (colorType === 4) {
      for (let x = 0; x < width; x++) {
        rgba[dst + x * 4] = out[x * 2];
        rgba[dst + x * 4 + 1] = out[x * 2];
        rgba[dst + x * 4 + 2] = out[x * 2];
        rgba[dst + x * 4 + 3] = out[x * 2 + 1];
      }
    } else {
      for (let x = 0; x < width; x++) {
        rgba[dst + x * 4] = out[x];
        rgba[dst + x * 4 + 1] = out[x];
        rgba[dst + x * 4 + 2] = out[x];
        rgba[dst + x * 4 + 3] = 255;
      }
    }
    prev = out;
  }
  return { width, height, rgba };
}

function pngChunk(type, data) {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, 'ascii');
  data.copy(out, 8);
  out.writeUInt32BE(crc32(out, 4, 8 + data.length), 8 + data.length);
  return out;
}

function writePng(width, height, colorType, plte, trns, idat) {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(width, 0);
  ihdr.writeUInt32BE(height, 4);
  ihdr[8] = 8; // bit depth
  ihdr[9] = colorType;
  ihdr[10] = 0; // compression
  ihdr[11] = 0; // filter
  ihdr[12] = 0; // interlace
  const parts = [Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]), pngChunk('IHDR', ihdr)];
  if (plte) parts.push(pngChunk('PLTE', plte));
  if (trns) parts.push(pngChunk('tRNS', trns));
  parts.push(pngChunk('IDAT', idat));
  parts.push(pngChunk('IEND', Buffer.alloc(0)));
  return Buffer.concat(parts);
}

// ---------------------------------------------------------------------------
// Image analysis
// ---------------------------------------------------------------------------

// Returns { opaque, grey, counts (Map word->count) or null when >256 colours,
//           key (24-bit RGB transparent-key value) or null }.
function analyze(rgba) {
  const n = rgba.length >> 2;
  let opaque = true;
  let grey = true;
  let counts = new Map();
  let distinct = 0;
  let keyRgb = -1;
  let keyPossible = true;
  for (let i = 0; i < n; i++) {
    const r = rgba[i * 4];
    const g = rgba[i * 4 + 1];
    const b = rgba[i * 4 + 2];
    const a = rgba[i * 4 + 3];
    if (a !== 255) opaque = false;
    if (r !== g || g !== b) grey = false;
    if (counts !== null) {
      const w = (r * 16777216 + g * 65536 + b * 256 + a) >>> 0;
      const c = counts.get(w);
      if (c === undefined) {
        distinct++;
        if (distinct > 256) {
          counts = null;
        } else {
          counts.set(w, 1);
        }
      } else {
        counts.set(w, c + 1);
      }
    }
    if (keyPossible) {
      if (a === 0) {
        const rgb = (r << 16) | (g << 8) | b;
        if (keyRgb === -1) keyRgb = rgb;
        else if (keyRgb !== rgb) keyPossible = false;
      } else if (a !== 255) {
        keyPossible = false;
      }
    }
  }
  let key = null;
  if (keyPossible && keyRgb !== -1) {
    // No opaque pixel may use the key colour.
    let clash = false;
    for (let i = 0; i < n; i++) {
      if (rgba[i * 4 + 3] === 255) {
        const rgb = (rgba[i * 4] << 16) | (rgba[i * 4 + 1] << 8) | rgba[i * 4 + 2];
        if (rgb === keyRgb) { clash = true; break; }
      }
    }
    if (!clash) key = keyRgb;
  }
  return { opaque, grey, counts, key };
}

// ---------------------------------------------------------------------------
// Forms (lossless re-representations of the same pixels)
// ---------------------------------------------------------------------------

function luminance(r, g, b) {
  return 299 * r + 587 * g + 114 * b;
}

// Build the palette form for one ordering. entries: [{word,r,g,b,a,count}].
// Transparent entries come first (alpha asc), then opaque entries in the
// chosen order, so tRNS stays short.
function paletteForm(width, height, rgba, entries, mode) {
  const transparent = entries.filter((e) => e.a < 255).sort((x, y) => (x.a - y.a) || (x.word - y.word));
  const opaqueEntries = entries.filter((e) => e.a === 255);
  if (mode === 'count') {
    opaqueEntries.sort((x, y) => (y.count - x.count) || (x.word - y.word));
  } else {
    opaqueEntries.sort((x, y) => (luminance(x.r, x.g, x.b) - luminance(y.r, y.g, y.b)) || (x.word - y.word));
  }
  const ordered = transparent.concat(opaqueEntries);
  const indexOf = new Map();
  for (let i = 0; i < ordered.length; i++) indexOf.set(ordered[i].word, i);
  const n = width * height;
  const pixels = Buffer.alloc(n);
  for (let i = 0; i < n; i++) {
    const w = (rgba[i * 4] * 16777216 + rgba[i * 4 + 1] * 65536 + rgba[i * 4 + 2] * 256 + rgba[i * 4 + 3]) >>> 0;
    pixels[i] = indexOf.get(w);
  }
  const plte = Buffer.alloc(ordered.length * 3);
  for (let i = 0; i < ordered.length; i++) {
    plte[i * 3] = ordered[i].r;
    plte[i * 3 + 1] = ordered[i].g;
    plte[i * 3 + 2] = ordered[i].b;
  }
  let trns = null;
  if (transparent.length > 0) {
    trns = Buffer.alloc(transparent.length);
    for (let i = 0; i < transparent.length; i++) trns[i] = ordered[i].a;
  }
  return { colorType: 3, bpp: 1, plte, trns, pixels };
}

function channelsForm(width, height, rgba, info) {
  const n = width * height;
  if (info.grey) {
    if (info.opaque || info.key !== null) {
      const pixels = Buffer.alloc(n);
      for (let i = 0; i < n; i++) pixels[i] = rgba[i * 4];
      const trns = info.key !== null ? Buffer.from([0, (info.key >> 16) & 0xFF]) : null;
      return { colorType: 0, bpp: 1, plte: null, trns, pixels };
    }
    const pixels = Buffer.alloc(n * 2);
    for (let i = 0; i < n; i++) {
      pixels[i * 2] = rgba[i * 4];
      pixels[i * 2 + 1] = rgba[i * 4 + 3];
    }
    return { colorType: 4, bpp: 2, plte: null, trns: null, pixels };
  }
  if (info.opaque || info.key !== null) {
    const pixels = Buffer.alloc(n * 3);
    for (let i = 0; i < n; i++) {
      pixels[i * 3] = rgba[i * 4];
      pixels[i * 3 + 1] = rgba[i * 4 + 1];
      pixels[i * 3 + 2] = rgba[i * 4 + 2];
    }
    const trns = info.key !== null
      ? Buffer.from([0, (info.key >> 16) & 0xFF, 0, (info.key >> 8) & 0xFF, 0, info.key & 0xFF])
      : null;
    return { colorType: 2, bpp: 3, plte: null, trns, pixels };
  }
  return { colorType: 6, bpp: 4, plte: null, trns: null, pixels: Buffer.from(rgba) };
}

// ---------------------------------------------------------------------------
// PNG row filters
// ---------------------------------------------------------------------------

function filterRow(row, prev, bpp, f) {
  const out = Buffer.alloc(row.length);
  if (f === 0) {
    row.copy(out);
    return out;
  }
  for (let i = 0; i < row.length; i++) {
    const left = i >= bpp ? row[i - bpp] : 0;
    const up = prev[i];
    let pred = 0;
    if (f === 1) pred = left;
    else if (f === 2) pred = up;
    else if (f === 3) pred = (left + up) >> 1;
    else pred = paeth(left, up, i >= bpp ? prev[i - bpp] : 0);
    out[i] = (row[i] - pred) & 0xFF;
  }
  return out;
}

function minsumScore(fr) {
  let s = 0;
  for (let i = 0; i < fr.length; i++) {
    const b = fr[i];
    s += b < 128 ? b : 256 - b;
  }
  return s;
}

const PAIR_SEEN = new Uint32Array(65536);
let pairToken = 0;

function pairsScore(fr) {
  pairToken++;
  let count = 0;
  for (let i = 0; i + 1 < fr.length; i++) {
    const p = (fr[i] << 8) | fr[i + 1];
    if (PAIR_SEEN[p] !== pairToken) {
      PAIR_SEEN[p] = pairToken;
      count++;
    }
  }
  return count;
}

// Filter every row of `pixels` (packed rows, no filter bytes) per `choice`:
// a fixed filter number, 'minsum', 'pairs', or 'brute' (per row, the filter
// whose single-row deflate at level 4 with the previous 32 KiB of filtered
// output as dictionary is smallest; ties go to the lower filter number).
// Returns the filtered stream (one filter-type byte per row).
function applyFilters(pixels, width, height, bpp, choice) {
  const stride = width * bpp;
  const out = Buffer.alloc(height * (stride + 1));
  let prev = Buffer.alloc(stride);
  for (let y = 0; y < height; y++) {
    const row = pixels.subarray(y * stride, (y + 1) * stride);
    const rows = [null, null, null, null, null];
    for (let f = 0; f < 5; f++) rows[f] = filterRow(row, prev, bpp, f);
    let f = 0;
    if (typeof choice === 'number') {
      f = choice;
    } else if (choice === 'minsum') {
      let best = Infinity;
      for (let c = 0; c < 5; c++) {
        const s = minsumScore(rows[c]);
        if (s < best) { best = s; f = c; }
      }
    } else if (choice === 'pairs') {
      let best = Infinity;
      for (let c = 0; c < 5; c++) {
        const s = pairsScore(rows[c]);
        if (s < best) { best = s; f = c; }
      }
    } else if (choice === 'brute') {
      const written = y * (stride + 1);
      const dict = out.subarray(Math.max(0, written - 32768), written);
      let best = Infinity;
      for (let c = 0; c < 5; c++) {
        const comp = deflateSync(rows[c], { level: 4, memLevel: 9, dictionary: dict });
        if (comp.length < best) { best = comp.length; f = c; }
      }
    }
    const off = y * (stride + 1);
    out[off] = f;
    rows[f].copy(out, off + 1);
    prev = row;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Screening and final deflate choice
// ---------------------------------------------------------------------------

// Screen one (form, filter-choice): zlib level 6. Returns the total cost
// (zlib bytes + PLTE/tRNS chunk overhead) plus the filtered stream and the
// level-6 stream, so the winner's stream can be reused.
function screenCandidate(form, width, height, choice) {
  const filtered = applyFilters(form.pixels, width, height, form.bpp, choice);
  const comp = deflateSync(filtered, { level: 6, memLevel: 8 });
  const overhead = (form.plte ? 12 + form.plte.length : 0) + (form.trns ? 12 + form.trns.length : 0);
  return { total: comp.length + overhead, filtered, comp, form };
}

// Best of three deflate streams for the winner's filtered bytes:
// the screen's level-6 stream, zlib level 9, and the optimal parser.
function bestDeflate(filtered, screenStream) {
  let best = screenStream;
  const l9 = deflateSync(filtered, { level: 9, memLevel: 9 });
  if (l9.length < best.length) best = l9;
  try {
    const opt = optimalDeflate(filtered);
    if (opt.length < best.length) best = opt;
  } catch (e) {
    // Never fail the whole run on the fancy path.
  }
  return best;
}

// ---------------------------------------------------------------------------
// One image, end to end
// ---------------------------------------------------------------------------

const PALETTE_BY_COUNT_FILTERS = [0];
const PALETTE_BY_LUM_FILTERS = [0, 'minsum', 'brute'];
const CHANNEL_FILTERS = [0, 1, 2, 4, 'minsum', 'pairs', 'brute'];

function encodeBest(width, height, rgba) {
  const info = analyze(rgba);
  let best = null;
  const consider = (candidate) => {
    if (best === null || candidate.total < best.total) best = candidate;
  };
  if (info.counts !== null) {
    const entries = [];
    for (const [word, count] of info.counts) {
      entries.push({
        word,
        r: (word >>> 24) & 0xFF,
        g: (word >>> 16) & 0xFF,
        b: (word >>> 8) & 0xFF,
        a: word & 0xFF,
        count,
      });
    }
    const byCount = paletteForm(width, height, rgba, entries, 'count');
    for (const choice of PALETTE_BY_COUNT_FILTERS) consider(screenCandidate(byCount, width, height, choice));
    const byLum = paletteForm(width, height, rgba, entries, 'lum');
    for (const choice of PALETTE_BY_LUM_FILTERS) consider(screenCandidate(byLum, width, height, choice));
    if (info.grey) {
      const greyForm = channelsForm(width, height, rgba, info);
      for (const choice of CHANNEL_FILTERS) consider(screenCandidate(greyForm, width, height, choice));
    }
  } else {
    const form = channelsForm(width, height, rgba, info);
    for (const choice of CHANNEL_FILTERS) consider(screenCandidate(form, width, height, choice));
  }
  const idat = bestDeflate(best.filtered, best.comp);
  return writePng(width, height, best.form.colorType, best.form.plte, best.form.trns, idat);
}

// ---------------------------------------------------------------------------
// Optimal-parsing deflate (zopfli-style, bounded)
// ---------------------------------------------------------------------------

function matchLengthAt(data, i, p, maxLen) {
  let l = 0;
  while (l + 4 <= maxLen) {
    if (data[i + l] !== data[p + l]) return l;
    if (data[i + l + 1] !== data[p + l + 1]) return l + 1;
    if (data[i + l + 2] !== data[p + l + 2]) return l + 2;
    if (data[i + l + 3] !== data[p + l + 3]) return l + 3;
    l += 4;
  }
  while (l < maxLen && data[i + l] === data[p + l]) l++;
  return l;
}

// For every position, record the longest match (ties: smallest distance) and
// the closest match (smallest distance with length >= 3) over two hash
// chains. Table A: 3-byte hash, chain cap by input size. Table B: 5-byte
// hash, cap 32, consulted only when A found a match shorter than 64.
function findMatches(data) {
  const n = data.length;
  const chainCap = n > 2000000 ? 32 : n > 800000 ? 64 : 128;
  const longestLen = new Uint16Array(n);
  const longestDist = new Int32Array(n);
  const closestLen = new Uint16Array(n);
  const closestDist = new Int32Array(n);
  const headA = new Int32Array(32768).fill(-1);
  const prevA = new Int32Array(n).fill(-1);
  const headB = new Int32Array(32768).fill(-1);
  const prevB = new Int32Array(n).fill(-1);
  for (let i = 0; i + 3 <= n; i++) {
    const maxLen = Math.min(258, n - i);
    let bestLen = 0;
    let bestDist = 0;
    let closeLen = 0;
    let closeDist = 0;
    // Table A (3-byte hash).
    const hA = ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & 0x7FFF;
    let p = headA[hA];
    let steps = 0;
    while (p >= 0 && steps < chainCap) {
      steps++;
      const dist = i - p;
      if (dist > 32768) break;
      const len = matchLengthAt(data, i, p, maxLen);
      if (len >= 3) {
        if (len > bestLen || (len === bestLen && dist < bestDist)) { bestLen = len; bestDist = dist; }
        if (closeDist === 0 || dist < closeDist) { closeLen = len; closeDist = dist; }
      }
      if (len >= 258 || bestLen >= 64) break;
      p = prevA[p];
    }
    prevA[i] = headA[hA];
    headA[hA] = i;
    // Table B (5-byte hash): searched only when A found a match shorter
    // than 64, but every position is still inserted into its chain.
    if (i + 5 <= n) {
      const hB = ((data[i] << 20) ^ (data[i + 1] << 15) ^ (data[i + 2] << 10) ^ (data[i + 3] << 5) ^ data[i + 4]) & 0x7FFF;
      if (bestLen < 64) {
        let q = headB[hB];
        let bsteps = 0;
        while (q >= 0 && bsteps < 32) {
          bsteps++;
          const dist = i - q;
          if (dist > 32768) break;
          const len = matchLengthAt(data, i, q, maxLen);
          if (len >= 3) {
            if (len > bestLen || (len === bestLen && dist < bestDist)) { bestLen = len; bestDist = dist; }
            if (closeDist === 0 || dist < closeDist) { closeLen = len; closeDist = dist; }
          }
          if (len >= 258 || bestLen >= 64) break;
          q = prevB[q];
        }
      }
      prevB[i] = headB[hB];
      headB[hB] = i;
    }
    longestLen[i] = bestLen;
    longestDist[i] = bestDist;
    closestLen[i] = closeLen;
    closestDist[i] = closeDist;
  }
  return { longestLen, longestDist, closestLen, closestDist };
}

function matchCost(len, dist, litLens, distLens) {
  const ll = litLens[257 + LEN_CODE[len]];
  const dl = distLens[DIST_CODE[dist]];
  if (ll === 0 || dl === 0) return Infinity;
  return ll + LEN_EXT[len] + dl + DIST_EXT[dist];
}

// Guarantee every byte value present in the block has a literal code, so the
// DP can always advance with a literal and no emitted symbol is codeless.
function ensureLiteralCoverage(lit, data, start, end) {
  for (let i = start; i < end; i++) {
    if (lit[data[i]] === 0) lit[data[i]] = 1;
  }
}

// Greedy parse of one block, for initial symbol frequencies.
function greedyFreqs(data, start, end, matches) {
  const lit = new Array(288).fill(0);
  const dist = new Array(30).fill(0);
  let i = start;
  while (i < end) {
    const ll = Math.min(matches.longestLen[i], end - i);
    if (ll >= 3) {
      lit[257 + LEN_CODE[ll]]++;
      dist[DIST_CODE[matches.longestDist[i]]]++;
      i += ll;
    } else {
      lit[data[i]]++;
      i++;
    }
  }
  lit[256]++;
  ensureLiteralCoverage(lit, data, start, end);
  return { lit, dist };
}

// Shortest-path optimal parse of one block. Per position, consider the
// literal, the longest match and the closest match (lengths clamped to the
// block end), priced with the given Huffman lengths.
function dpParse(data, start, end, matches, litLens, distLens) {
  const n = end - start;
  const cost = new Float64Array(n + 1);
  for (let i = 0; i <= n; i++) cost[i] = Infinity;
  cost[0] = 0;
  const choice = new Int8Array(n + 1); // 0 literal, 1 longest, 2 closest
  const choiceLen = new Int32Array(n + 1);
  const choiceDist = new Int32Array(n + 1);
  for (let i = 0; i < n; i++) {
    const base = cost[i];
    if (base === Infinity) continue;
    const pos = start + i;
    const lc = base + litLens[data[pos]];
    if (lc < cost[i + 1]) {
      cost[i + 1] = lc;
      choice[i + 1] = 0;
      choiceLen[i + 1] = 1;
    }
    const ll = Math.min(matches.longestLen[pos], n - i);
    if (ll >= 3) {
      const c = base + matchCost(ll, matches.longestDist[pos], litLens, distLens);
      if (c < cost[i + ll]) {
        cost[i + ll] = c;
        choice[i + ll] = 1;
        choiceLen[i + ll] = ll;
        choiceDist[i + ll] = matches.longestDist[pos];
      }
    }
    const cl = Math.min(matches.closestLen[pos], n - i);
    if (cl >= 3) {
      const c = base + matchCost(cl, matches.closestDist[pos], litLens, distLens);
      if (c < cost[i + cl]) {
        cost[i + cl] = c;
        choice[i + cl] = 2;
        choiceLen[i + cl] = cl;
        choiceDist[i + cl] = matches.closestDist[pos];
      }
    }
  }
  const ops = [];
  let i = n;
  while (i > 0) {
    const ch = choice[i];
    if (ch === 0) {
      ops.push({ lit: data[start + i - 1] });
      i -= 1;
    } else {
      const len = choiceLen[i];
      ops.push({ len, dist: choiceDist[i] });
      i -= len;
    }
  }
  ops.reverse();
  return ops;
}

function freqsFromOps(ops, data, start, end) {
  const lit = new Array(288).fill(0);
  const dist = new Array(30).fill(0);
  for (const op of ops) {
    if (op.len === undefined) {
      lit[op.lit]++;
    } else {
      lit[257 + LEN_CODE[op.len]]++;
      dist[DIST_CODE[op.dist]]++;
    }
  }
  lit[256]++;
  ensureLiteralCoverage(lit, data, start, end);
  return { lit, dist };
}

// RLE-encode a code-length array with symbols 16 (repeat previous 3-6),
// 17 (repeat 0, 3-10) and 18 (repeat 0, 11-138).
function rleLengths(arr) {
  const items = [];
  let i = 0;
  while (i < arr.length) {
    const v = arr[i];
    let run = 1;
    while (i + run < arr.length && arr[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) {
        const take = Math.min(r, 138);
        items.push({ sym: 18, extra: take - 11, extraBits: 7 });
        r -= take;
      }
      if (r >= 3) {
        items.push({ sym: 17, extra: r - 3, extraBits: 3 });
        r = 0;
      }
      while (r > 0) {
        items.push({ sym: 0, extra: 0, extraBits: 0 });
        r--;
      }
    } else {
      items.push({ sym: v, extra: 0, extraBits: 0 });
      let r = run - 1;
      while (r >= 3) {
        const take = Math.min(r, 6);
        items.push({ sym: 16, extra: take - 3, extraBits: 2 });
        r -= take;
      }
      while (r > 0) {
        items.push({ sym: v, extra: 0, extraBits: 0 });
        r--;
      }
    }
    i += run;
  }
  return items;
}

function blockOpsBits(ops, litLens, distLens) {
  let bits = 0;
  for (const op of ops) {
    if (op.len === undefined) {
      bits += litLens[op.lit];
    } else {
      bits += litLens[257 + LEN_CODE[op.len]] + LEN_EXT[op.len] + distLens[DIST_CODE[op.dist]] + DIST_EXT[op.dist];
    }
  }
  return bits;
}

function emitOps(bw, ops, litCodes, distCodes, litLens, distLens) {
  for (const op of ops) {
    if (op.len === undefined) {
      bw.putCode(litCodes[op.lit], litLens[op.lit]);
    } else {
      const li = LEN_CODE[op.len];
      const di = DIST_CODE[op.dist];
      bw.putCode(litCodes[257 + li], litLens[257 + li]);
      if (LEN_EXT[op.len] > 0) bw.putBits(op.len - LEN_BASE[li], LEN_EXT[op.len]);
      bw.putCode(distCodes[di], distLens[di]);
      if (DIST_EXT[op.dist] > 0) bw.putBits(op.dist - DIST_BASE[di], DIST_EXT[op.dist]);
    }
  }
  bw.putCode(litCodes[256], litLens[256]);
}

// Emit one block, choosing dynamic vs fixed Huffman by exact bit count.
function emitBlock(bw, ops, litLens, distLens, isLast) {
  const litCodes = canonicalCodes(litLens);
  const distCodes = canonicalCodes(distLens);
  const opsBitsDynamic = blockOpsBits(ops, litLens, distLens);
  let hlit = 257;
  for (let i = 287; i >= 257; i--) {
    if (litLens[i] > 0) { hlit = i + 1; break; }
  }
  let hdist = 1;
  for (let i = 29; i >= 1; i--) {
    if (distLens[i] > 0) { hdist = i + 1; break; }
  }
  const combined = litLens.slice(0, hlit).concat(distLens.slice(0, hdist));
  const items = rleLengths(combined);
  const clFreq = new Array(19).fill(0);
  for (const it of items) clFreq[it.sym]++;
  const clLens = huffmanLengths(clFreq, 7);
  const clCodes = canonicalCodes(clLens);
  let hclen = 4;
  for (let j = 0; j < 19; j++) {
    if (clLens[CL_ORDER[j]] > 0) hclen = Math.max(hclen, j + 1);
  }
  let clBits = 0;
  for (const it of items) clBits += clLens[it.sym] + it.extraBits;
  const dynamicBits = 3 + 5 + 5 + 4 + 3 * hclen + clBits + opsBitsDynamic + litLens[256];
  const fixedLitCodes = canonicalCodes(FIXED_LIT_LENS);
  const fixedDistCodes = canonicalCodes(FIXED_DIST_LENS);
  const fixedBits = 3 + blockOpsBits(ops, FIXED_LIT_LENS, FIXED_DIST_LENS) + FIXED_LIT_LENS[256];
  if (dynamicBits < fixedBits) {
    bw.putBits(isLast ? 1 : 0, 1);
    bw.putBits(2, 2);
    bw.putBits(hlit - 257, 5);
    bw.putBits(hdist - 1, 5);
    bw.putBits(hclen - 4, 4);
    for (let j = 0; j < hclen; j++) bw.putBits(clLens[CL_ORDER[j]], 3);
    for (const it of items) {
      bw.putCode(clCodes[it.sym], clLens[it.sym]);
      if (it.extraBits > 0) bw.putBits(it.extra, it.extraBits);
    }
    emitOps(bw, ops, litCodes, distCodes, litLens, distLens);
  } else {
    bw.putBits(isLast ? 1 : 0, 1);
    bw.putBits(1, 2);
    emitOps(bw, ops, fixedLitCodes, fixedDistCodes, FIXED_LIT_LENS, FIXED_DIST_LENS);
  }
}

// Optimal-parsing deflate of the whole filtered stream: blocks of 131072
// bytes; per block, greedy frequencies -> lengths -> DP -> rebuild lengths
// -> DP again -> emit. Returns a complete zlib stream (0x78 0xDA header,
// deflate blocks, Adler-32 trailer).
function optimalDeflate(data) {
  const matches = findMatches(data);
  const bw = new BitWriter();
  const BLOCK = 131072;
  for (let start = 0; start < data.length; start += BLOCK) {
    const end = Math.min(start + BLOCK, data.length);
    const isLast = end === data.length;
    const g = greedyFreqs(data, start, end, matches);
    let litLens = huffmanLengths(g.lit, 15);
    let distLens = huffmanLengths(g.dist, 15);
    let ops = dpParse(data, start, end, matches, litLens, distLens);
    const f2 = freqsFromOps(ops, data, start, end);
    litLens = huffmanLengths(f2.lit, 15);
    distLens = huffmanLengths(f2.dist, 15);
    ops = dpParse(data, start, end, matches, litLens, distLens);
    // Rebuild the code lengths from the final ops, so the emitted block's
    // tables cover exactly the symbols it emits.
    const f3 = freqsFromOps(ops, data, start, end);
    litLens = huffmanLengths(f3.lit, 15);
    distLens = huffmanLengths(f3.dist, 15);
    emitBlock(bw, ops, litLens, distLens, isLast);
  }
  const deflated = bw.finish();
  const out = Buffer.alloc(2 + deflated.length + 4);
  out[0] = 0x78;
  out[1] = 0xDA;
  deflated.copy(out, 2);
  out.writeUInt32BE(adler32(data), 2 + deflated.length);
  return out;
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(INPUT_DIR).sort()) {
  const buf = readFileSync(join(INPUT_DIR, id, 'image.png'));
  const img = decodePng(buf);
  const png = encodeBest(img.width, img.height, img.rgba);
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'image.png'), png);
}
