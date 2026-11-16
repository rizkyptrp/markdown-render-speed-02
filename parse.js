// parse.js — a fast, dependency-free CommonMark + GFM parser whose output
// matches marked 18.1.3 (default options) byte for byte.
//
// Written from scratch from observed input/output behaviour. Structure:
//   * block parser: line-by-line, container stack (blockquote / list / item),
//     lazy continuation, link reference definitions collected globally.
//   * inline parser: single scan building items (text, delimiter runs,
//     code spans, links, autolinks, HTML), emphasis resolved per segment
//     with the delimiter-stack algorithm, GFM emails resolved after
//     emphasis so emphasis wins over an email local part.

export function parse(markdown) {
  inLinkGlobal = false;
  return new DocParser(markdown).run();
}

// Marked tracks an "inside a link" state from inline <a> tags that
// persists across blocks: once an unclosed <a> open tag is seen, bare
// autolinks and emails are suppressed for the rest of the document
// (angle autolinks still form), until an inline </a> clears it. HTML
// blocks do not affect it. Reset per parse() call above.
let inLinkGlobal = false;

// For an inline HTML tag string, return true if it opens an <a> (sets
// inLink), false if it closes one (clears inLink), null otherwise.
// `<a/>` (slash immediately after the name/attrs) is self-closing and
// does not open; `<a />` (whitespace before the slash) DOES open.
function htmlLinkState(tag) {
  if (tag.length < 3 || tag.charCodeAt(0) !== 60) return null;
  let j = 1;
  let closing = false;
  if (tag.charCodeAt(j) === 47) { closing = true; j++; }
  const c = tag.charCodeAt(j);
  if (c !== 97 && c !== 65) return null;
  const after = j + 1 < tag.length ? tag.charCodeAt(j + 1) : -1;
  if (after !== 62 && after !== 32 && after !== 9 && after !== 47 && after !== 10) return null;
  if (closing) return false;
  // Self-closing only when the tag ends with `/>` and the char before
  // the slash is not whitespace.
  if (tag.length >= 2 && tag.charCodeAt(tag.length - 1) === 62 &&
      tag.charCodeAt(tag.length - 2) === 47) {
    const before = tag.length >= 3 ? tag.charCodeAt(tag.length - 3) : -1;
    if (before !== 32 && before !== 9 && before !== 10) return null;
  }
  return true;
}

// ---------------------------------------------------------------------------
// Character classification
// ---------------------------------------------------------------------------

// ASCII punctuation set (Unicode P within ASCII).
const ASCII_PUNCT = new Uint8Array(128);
for (const c of '!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~') ASCII_PUNCT[c.charCodeAt(0)] = 1;

const RE_NONASCII_PUNCT = /[\p{P}\p{S}]/u;
const RE_NONASCII_SPACE = /^[\u00a0\u1680\u2000-\u200a\u202f\u205f\u3000]$/u;

function isPunctCode(cp) {
  if (cp < 128) return ASCII_PUNCT[cp] === 1;
  return RE_NONASCII_PUNCT.test(String.fromCodePoint(cp));
}

// Unicode whitespace for flanking: Zs + tab, LF, FF, CR.
function isSpaceCode(cp) {
  if (cp === 0x20 || cp === 0x09 || cp === 0x0a || cp === 0x0c || cp === 0x0d) return true;
  if (cp < 128) return false;
  return RE_NONASCII_SPACE.test(String.fromCodePoint(cp));
}

function isWordCode(cp) {
  return (cp >= 48 && cp <= 57) || (cp >= 65 && cp <= 90) || (cp >= 97 && cp <= 122) || cp === 95;
}

function isAlnumCode(cp) {
  return (cp >= 48 && cp <= 57) || (cp >= 65 && cp <= 90) || (cp >= 97 && cp <= 122);
}

function isDigitCode(cp) {
  return cp >= 48 && cp <= 57;
}

// Code point at index i of string s (handles lone surrogates as the unit).
function codeAt(s, i) {
  const c = s.charCodeAt(i);
  if (c >= 0xd800 && c <= 0xdbff && i + 1 < s.length) {
    const d = s.charCodeAt(i + 1);
    if (d >= 0xdc00 && d <= 0xdfff) return ((c - 0xd800) << 10) + (d - 0xdc00) + 0x10000;
  }
  return c;
}

// ---------------------------------------------------------------------------
// Escaping. Three flavours, as observed from marked:
//   1. text/alt:  numeric entities DECODED, named &word; passed through,
//      other & escaped; < > " ' escaped.
//   2. href/title/lang: entities (named and numeric) passed through
//      verbatim, other & escaped; < > " ' escaped. No decoding.
//   3. unconditional (code, autolinks): & always escaped, plus < > " '.
// ---------------------------------------------------------------------------

const ESC_TEXT = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

function decodeNumericEntity(s, i) {
  // s[i] === '&', s[i+1] === '#'. Returns [decodedCharOrNull, endIndex].
  let j = i + 2;
  let hex = false;
  if (j < s.length && (s[j] === 'x' || s[j] === 'X')) { hex = true; j++; }
  const maxDigits = hex ? 6 : 7;
  let val = 0;
  let digits = 0;
  while (j < s.length && digits < maxDigits) {
    const c = s.charCodeAt(j);
    let d = -1;
    if (c >= 48 && c <= 57) d = c - 48;
    else if (hex && c >= 97 && c <= 102) d = c - 87;
    else if (hex && c >= 65 && c <= 70) d = c - 55;
    else break;
    val = val * (hex ? 16 : 10) + d;
    digits++;
    j++;
  }
  if (digits === 0) return null;
  if (j < s.length && s.charCodeAt(j) >= 48 && s.charCodeAt(j) <= 57) return null;
  if (hex && j < s.length) {
    const c = s.charCodeAt(j);
    if ((c >= 48 && c <= 57) || (c >= 97 && c <= 102) || (c >= 65 && c <= 70)) return null;
  }
  if (j >= s.length || s[j] !== ';') return null;
  let cp = val;
  if (cp === 0 || (cp >= 0xd800 && cp <= 0xdfff) || cp > 0x10ffff) cp = 0xfffd;
  return [String.fromCodePoint(cp), j + 1];
}

// Scan a named entity &word; starting at i (s[i] === '&'). Returns end
// index (exclusive) if valid, else -1. No decoding, just pass-through.
function namedEntityEnd(s, i) {
  let j = i + 1;
  const n = s.length;
  while (j < n && isWordCode(s.charCodeAt(j))) j++;
  if (j > i + 1 && j < n && s[j] === ';') return j + 1;
  return -1;
}

// Numeric entity end (for flavour 2, no decode). Returns end index or -1.
function numericEntityEnd(s, i) {
  let j = i + 2;
  const n = s.length;
  let hex = false;
  if (j < n && (s[j] === 'x' || s[j] === 'X')) { hex = true; j++; }
  const maxDigits = hex ? 6 : 7;
  let digits = 0;
  while (j < n && digits < maxDigits) {
    const c = s.charCodeAt(j);
    const ok = (c >= 48 && c <= 57) ||
      (hex && ((c >= 97 && c <= 102) || (c >= 65 && c <= 70)));
    if (!ok) break;
    digits++;
    j++;
  }
  if (digits === 0) return -1;
  if (j < n) {
    const c = s.charCodeAt(j);
    if ((c >= 48 && c <= 57) || (hex && ((c >= 97 && c <= 102) || (c >= 65 && c <= 70)))) return -1;
  }
  if (j < n && s[j] === ';') return j + 1;
  return -1;
}

function escapeText(s) {
  const n = s.length;
  let out = null;
  let last = 0;
  for (let i = 0; i < n; i++) {
    const c = s[i];
    if (c === '&') {
      let end = -1;
      let repl = null;
      if (i + 1 < n && s[i + 1] === '#') {
        const dec = decodeNumericEntity(s, i);
        if (dec) {
          end = dec[1];
          repl = ESC_TEXT[dec[0]] || dec[0];
        }
      } else {
        end = namedEntityEnd(s, i);
        if (end !== -1) {
          i = end - 1;
          continue; // pass through verbatim
        }
      }
      if (end === -1) {
        if (out === null) { out = []; if (i > 0) out.push(s.slice(0, i)); }
        else if (i > last) out.push(s.slice(last, i));
        out.push('&amp;');
        last = i + 1;
      } else {
        if (out === null) { out = []; if (i > 0) out.push(s.slice(0, i)); }
        else if (i > last) out.push(s.slice(last, i));
        out.push(repl);
        last = end;
        i = end - 1;
      }
    } else if (c === '<' || c === '>' || c === '"' || c === "'") {
      if (out === null) { out = []; if (i > 0) out.push(s.slice(0, i)); }
      else if (i > last) out.push(s.slice(last, i));
      out.push(ESC_TEXT[c]);
      last = i + 1;
    }
  }
  if (out === null) return s;
  if (last < n) out.push(s.slice(last));
  return out.join('');
}

function escapeHref(s) {
  const n = s.length;
  let out = null;
  let last = 0;
  for (let i = 0; i < n; i++) {
    const c = s[i];
    if (c === '&') {
      let end = -1;
      if (i + 1 < n && s[i + 1] === '#') end = numericEntityEnd(s, i);
      else end = namedEntityEnd(s, i);
      if (end !== -1) { i = end - 1; continue; }
      if (out === null) { out = []; if (i > 0) out.push(s.slice(0, i)); }
      else if (i > last) out.push(s.slice(last, i));
      out.push('&amp;');
      last = i + 1;
    } else if (c === '<' || c === '>' || c === '"' || c === "'") {
      if (out === null) { out = []; if (i > 0) out.push(s.slice(0, i)); }
      else if (i > last) out.push(s.slice(last, i));
      out.push(ESC_TEXT[c]);
      last = i + 1;
    }
  }
  if (out === null) return s;
  if (last < n) out.push(s.slice(last));
  return out.join('');
}

function escapeUncond(s) {
  const n = s.length;
  let out = null;
  let last = 0;
  for (let i = 0; i < n; i++) {
    const c = s[i];
    if (c === '&' || c === '<' || c === '>' || c === '"' || c === "'") {
      if (out === null) { out = []; if (i > 0) out.push(s.slice(0, i)); }
      else if (i > last) out.push(s.slice(last, i));
      out.push(ESC_TEXT[c]);
      last = i + 1;
    }
  }
  if (out === null) return s;
  if (last < n) out.push(s.slice(last));
  return out.join('');
}

// ---------------------------------------------------------------------------
// URLs
// ---------------------------------------------------------------------------

function cleanUrl(href) {
  try {
    return encodeURI(href).replace(/%25/g, '%');
  } catch (_e) {
    return null; // lone surrogate: link renders as text only
  }
}

// ---------------------------------------------------------------------------
// Link label normalisation: full case fold (toLowerCase + the code points
// where full fold differs), collapse whitespace runs to one space, trim.
// ---------------------------------------------------------------------------

const FULL_FOLD_EXTRA = new Map([
  [0x00df, 'ss'],
  [0xfb00, 'ff'], [0xfb01, 'fi'], [0xfb02, 'fl'], [0xfb03, 'ffi'],
  [0xfb04, 'ffl'], [0xfb05, 'st'], [0xfb06, 'st'],
  [0xfb13, '\u0574\u0576'], [0xfb14, '\u0574\u0565'], [0xfb15, '\u0574\u056b'],
  [0xfb16, '\u057e\u0576'], [0xfb17, '\u0574\u056d'],
  [0x0390, '\u03b9\u0308\u0301'], [0x03b0, '\u03c5\u0308\u0301'],
  [0x0149, '\u02bcn'], [0x01f0, 'j\u030c'], [0x0587, '\u0565\u0582'],
]);

function normalizeLabel(raw) {
  let s = raw.toLowerCase();
  // Apply full-fold extras where present.
  let folded = null;
  for (let i = 0; i < s.length; i++) {
    const cp = codeAt(s, i);
    const rep = FULL_FOLD_EXTRA.get(cp);
    if (rep !== undefined) {
      if (folded === null) folded = s.slice(0, i);
      folded += rep;
      if (cp > 0xffff) i++;
    } else if (folded !== null) {
      folded += s[i];
      if (cp > 0xffff) { folded += s[i + 1]; i++; }
    }
  }
  if (folded !== null) s = folded;
  // Collapse whitespace (JS \s, as in the reference) and trim.
  return s.replace(/\s+/g, ' ').trim();
}

// Backslash unescaping inside destinations and titles: \<punct> -> <punct>.
function unescapeInline(s) {
  if (s.indexOf('\\') === -1) return s;
  let out = '';
  let last = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\' && i + 1 < s.length && isPunctCode(s.charCodeAt(i + 1))) {
      out += s.slice(last, i) + s[i + 1];
      i++;
      last = i + 1;
    }
  }
  return out + s.slice(last);
}

function stripTrailingWs(s) {
  let end = s.length;
  while (end > 0) {
    const c = s.charCodeAt(end - 1);
    if (c !== 32 && c !== 9) break;
    end--;
  }
  return end === s.length ? s : s.slice(0, end);
}

function trimWs(s) {
  let start = 0;
  let end = s.length;
  while (start < end) {
    const c = s.charCodeAt(start);
    if (c !== 32 && c !== 9) break;
    start++;
  }
  while (end > start) {
    const c = s.charCodeAt(end - 1);
    if (c !== 32 && c !== 9) break;
    end--;
  }
  return s.slice(start, end);
}

// Is the line a setext underline (any leading whitespace, =+ or exactly --,
// trailing whitespace only)?
function isSetextLine(s) {
  let i = 0;
  while (i < s.length && (s.charCodeAt(i) === 32 || s.charCodeAt(i) === 9)) i++;
  if (i >= s.length) return false;
  const c = s.charCodeAt(i);
  if (c !== 61 && c !== 45) return false;
  let j = i;
  while (j < s.length && s.charCodeAt(j) === c) j++;
  const runLen = j - i;
  if (c === 45 && runLen !== 2) return false;
  while (j < s.length) {
    const cc = s.charCodeAt(j);
    if (cc !== 32 && cc !== 9) return false;
    j++;
  }
  return true;
}

// Expand the leading tabs of a paragraph line to spaces, given the column
// at which the line's content starts.
function expandLeadingTabs(s, startCol) {
  let col = startCol;
  let i = 0;
  let out = '';
  let changed = false;
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === 32) { out += ' '; col++; i++; }
    else if (c === 9) { const w = 4 - (col % 4); out += ' '.repeat(w); col += w; i++; changed = true; }
    else break;
  }
  if (!changed) return s;
  return out + s.slice(i);
}

// ---------------------------------------------------------------------------
// Inline parsing
// ---------------------------------------------------------------------------
// Item kinds: 0 text, 1 delimiter, 2 link, 3 image, 4 code span, 5 raw html,
// 6 autolink, 7 hard break, 8 unmatched bracket, 9 email link.

function codeBefore(s, i) {
  if (i <= 0) return -1;
  const c = s.charCodeAt(i - 1);
  if (c >= 0xdc00 && c <= 0xdfff && i >= 2) {
    const h = s.charCodeAt(i - 2);
    if (h >= 0xd800 && h <= 0xdbff) return ((h - 0xd800) << 10) + (c - 0xdc00) + 0x10000;
  }
  return c;
}

function isAsciiLetter(c) {
  return (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}

function isAsciiAlnum(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}

function isEmailLocalChar(c) {
  return isWordCode(c) || c === 46 || c === 43 || c === 45;
}

// atext set for <...> email local parts, minus '^' (observed).
function isAngleEmailLocal(c) {
  if (isWordCode(c)) return true;
  return c === 33 || c === 35 || c === 36 || c === 37 || c === 38 || c === 39 ||
    c === 42 || c === 43 || c === 45 || c === 46 || c === 47 || c === 61 ||
    c === 63 || c === 95 || c === 96 || c === 123 || c === 124 || c === 125 || c === 126;
}

function flanking(s, i, len) {
  const n = s.length;
  let beforeSpace, beforePunct, afterSpace, afterPunct;
  if (i === 0) { beforeSpace = true; beforePunct = false; }
  else {
    const cp = codeBefore(s, i);
    beforeSpace = isSpaceCode(cp);
    beforePunct = isPunctCode(cp);
  }
  const afterIdx = i + len;
  if (afterIdx >= n) { afterSpace = true; afterPunct = false; }
  else {
    const cp = codeAt(s, afterIdx);
    afterSpace = isSpaceCode(cp);
    afterPunct = isPunctCode(cp);
  }
  const left = !afterSpace && (!afterPunct || beforeSpace || beforePunct);
  const right = !beforeSpace && (!beforePunct || afterSpace || afterPunct);
  return { left, right, beforePunct, afterPunct };
}

// Email domain: [\w-]+ (\.[\w-]*[A-Za-z0-9])+ with lookahead (?![\w-]).
// Returns end index or -1.
function matchEmailDomain(s, i) {
  const n = s.length;
  let j = i;
  while (j < n) {
    const c = s.charCodeAt(j);
    if (isWordCode(c) || c === 45) j++;
    else break;
  }
  if (j === i) return -1;
  let groups = 0;
  while (j < n && s.charCodeAt(j) === 46) {
    let k = j + 1;
    let lastAlnum = -1;
    while (k < n) {
      const c = s.charCodeAt(k);
      if (isWordCode(c) || c === 45) {
        if (isAlnumCode(c)) lastAlnum = k;
        k++;
      } else break;
    }
    if (lastAlnum === -1) break;
    j = lastAlnum + 1;
    groups++;
  }
  if (groups === 0) return -1;
  if (j < n) {
    const c = s.charCodeAt(j);
    if (isWordCode(c) || c === 45) return -1;
  }
  return j;
}

const TRIM_PUNCT = new Set(['?', '!', '.', ',', ':', ';', '*', '_', '~', "'", '"']);

function trimAutolink(url) {
  let changed = true;
  while (changed) {
    changed = false;
    // Entity check FIRST: a trailing ';' trimmed as punctuation would
    // destroy the entity (e.g. '&hl;' must leave the link whole).
    if (url.length > 0 && url[url.length - 1] === ';') {
      const amp = url.lastIndexOf('&');
      if (amp !== -1 && amp + 1 < url.length - 1) {
        let ok = true;
        for (let k = amp + 1; k < url.length - 1; k++) {
          if (!isWordCode(url.charCodeAt(k))) { ok = false; break; }
        }
        if (ok) {
          url = url.slice(0, amp);
          changed = true;
        }
      }
    }
    while (url.length > 0 && TRIM_PUNCT.has(url[url.length - 1])) {
      url = url.slice(0, -1);
      changed = true;
    }
    if (url.length > 0 && url[url.length - 1] === ')') {
      const lastOpen = url.lastIndexOf('(');
      if (lastOpen === -1) {
        url = url.slice(0, -1);
        changed = true;
      } else {
        let count = 0;
        for (let k = lastOpen + 1; k < url.length; k++) if (url[k] === ')') count++;
        if (count >= 2) {
          url = url.slice(0, -1);
          changed = true;
        }
      }
    }
    const lastClose = url.lastIndexOf(')');
    const firstOpen = url.indexOf('(', lastClose + 1);
    if (firstOpen !== -1) {
      url = url.slice(0, firstOpen);
      changed = true;
    }
  }
  return url;
}

function matchAutolink(s, i, limit) {
  const n = s.length;
  const end = limit === undefined ? n : Math.min(n, limit);
  const c = s.charCodeAt(i);
  if (c === 119 && s.startsWith('www.', i)) { // www.
    if (i > 0) {
      const pc = s.charCodeAt(i - 1);
      if (!(pc === 32 || pc === 9 || pc === 10 || pc === 40 || pc === 42 || pc === 95 || pc === 126)) return null;
    }
    const start = i + 4;
    if (start >= end) return null;
    const sc = s.charCodeAt(start);
    if (!isWordCode(sc) && sc !== 45) return null;
    let j = start;
    while (j < end) {
      const cc = s.charCodeAt(j);
      if (cc === 32 || cc === 9 || cc === 10 || cc === 60 || cc < 32 || cc === 127) break;
      j++;
    }
    const url = trimAutolink(s.slice(i, j));
    if (url.length <= 4) return null;
    return ['http://' + url, url, i + url.length];
  }
  if (c === 104 || c === 72 || c === 102 || c === 70) { // http/https/ftp
    let prefixLen = 0;
    // Case-insensitive prefix check without slice+toLowerCase allocation.
    const c1 = s.charCodeAt(i + 1) | 32, c2 = s.charCodeAt(i + 2) | 32, c3 = s.charCodeAt(i + 3) | 32;
    if ((c | 32) === 104 && c1 === 116 && c2 === 116 && c3 === 112) { // http
      if (s.charCodeAt(i + 4) === 58 && s.charCodeAt(i + 5) === 47 && s.charCodeAt(i + 6) === 47) prefixLen = 7;
      else if ((s.charCodeAt(i + 4) | 32) === 115 && s.charCodeAt(i + 5) === 58 && s.charCodeAt(i + 6) === 47 && s.charCodeAt(i + 7) === 47) prefixLen = 8;
      else return null;
    } else if ((c | 32) === 102 && c1 === 116 && c2 === 112 && s.charCodeAt(i + 3) === 58 && s.charCodeAt(i + 4) === 47 && s.charCodeAt(i + 5) === 47) { // ftp://
      prefixLen = 6;
    } else return null;
    const start = i + prefixLen;
    if (start >= end) return null;
    const sc = s.charCodeAt(start);
    if (!isWordCode(sc) && sc !== 45) return null;
    let j = start;
    while (j < end) {
      const cc = s.charCodeAt(j);
      if (cc === 32 || cc === 9 || cc === 10 || cc === 60 || cc < 32 || cc === 127) break;
      j++;
    }
    const url = trimAutolink(s.slice(i, j));
    return [url, url, i + url.length];
  }
  if (c === 109 && s.startsWith('mailto:', i)) { // mailto: (lowercase only)
    if (i > 0 && isAsciiAlnum(s.charCodeAt(i - 1))) return null;
    const emailStart = i + 7;
    let k = emailStart;
    while (k < n && isEmailLocalChar(s.charCodeAt(k))) k++;
    if (k === emailStart || k >= n || s.charCodeAt(k) !== 64) return null;
    const domEnd = matchEmailDomain(s, k + 1);
    if (domEnd === -1) return null;
    const url = s.slice(i, domEnd);
    return [url, url, domEnd];
  }
  if (c === 120 && s.startsWith('xmpp:', i)) { // xmpp: (lowercase only)
    if (i > 0 && isAsciiAlnum(s.charCodeAt(i - 1))) return null;
    const emailStart = i + 5;
    let k = emailStart;
    while (k < n && isEmailLocalChar(s.charCodeAt(k))) k++;
    if (k === emailStart || k >= n || s.charCodeAt(k) !== 64) return null;
    const domEnd = matchEmailDomain(s, k + 1);
    if (domEnd === -1) return null;
    let end = domEnd;
    // Optional single path segment: '/' + [A-Za-z0-9.@]+, no trailing '.'.
    if (end < n && s.charCodeAt(end) === 47) {
      let p = end + 1;
      while (p < n) {
        const cc = s.charCodeAt(p);
        if (isAsciiAlnum(cc) || cc === 46 || cc === 64) p++;
        else break;
      }
      while (p > end + 1 && s.charCodeAt(p - 1) === 46) p--;
      if (p > end + 1) end = p;
    }
    const url = s.slice(i, end);
    return [url, url, end];
  }
  return null;
}

function parseCodeSpan(s, i) {
  const n = s.length;
  let j = i;
  while (j < n && s.charCodeAt(j) === 96) j++;
  const runLen = j - i;
  let k = j;
  while (k < n) {
    if (s.charCodeAt(k) === 96) {
      let m = k;
      while (m < n && s.charCodeAt(m) === 96) m++;
      if (m - k === runLen) {
        let content = s.slice(j, k);
        if (content.indexOf('\n') !== -1) content = content.replace(/\n/g, ' ');
        if (content.length >= 2 && content.charCodeAt(0) === 32 &&
            content.charCodeAt(content.length - 1) === 32) {
          let allSpace = true;
          for (let p = 0; p < content.length; p++) {
            if (content.charCodeAt(p) !== 32) { allSpace = false; break; }
          }
          if (!allSpace) content = content.slice(1, -1);
        }
        return [content, m];
      }
      k = m;
    } else {
      k++;
    }
  }
  return null;
}

function parseInlineHtml(s, i) {
  const n = s.length;
  if (i + 1 >= n) return null;
  const c1 = s.charCodeAt(i + 1);
  if (c1 === 33) { // !
    if (s.startsWith('<!--', i)) {
      if (s.startsWith('<!-->', i)) return ['<!-->', i + 5];
      if (s.startsWith('<!--->', i)) return ['<!--->', i + 6];
      const end = s.indexOf('-->', i + 4);
      if (end !== -1) return [s.slice(i, end + 3), end + 3];
      return null;
    }
    if (s.startsWith('<![CDATA[', i)) {
      const end = s.indexOf(']]>', i + 9);
      if (end !== -1) return [s.slice(i, end + 3), end + 3];
      return null;
    }
    if (i + 2 < n && isAsciiLetter(s.charCodeAt(i + 2))) {
      const end = s.indexOf('>', i + 3);
      if (end !== -1) return [s.slice(i, end + 1), end + 1];
      return null;
    }
    return null;
  }
  if (c1 === 63) { // ?
    const end = s.indexOf('?>', i + 2);
    if (end !== -1) return [s.slice(i, end + 2), end + 2];
    return null;
  }
  if (c1 === 47) { // / close tag
    let j = i + 2;
    while (j < n && isAsciiLetter(s.charCodeAt(j))) j++;
    if (j === i + 2) return null;
    let k = j;
    while (k < n && (s[k] === ' ' || s[k] === '\t' || s[k] === '\n')) k++;
    if (k < n && s[k] === '>') return [s.slice(i, k + 1), k + 1];
    return null;
  }
  if (isAsciiLetter(c1)) { // open tag
    let j = i + 1;
    while (j < n) {
      const cc = s.charCodeAt(j);
      if (isAsciiLetter(cc) || (cc >= 48 && cc <= 57) || cc === 45) j++;
      else break;
    }
    while (true) {
      const wsStart = j;
      while (j < n && (s[j] === ' ' || s[j] === '\t' || s[j] === '\n')) j++;
      if (j >= n) return null;
      if (s[j] === '>') return [s.slice(i, j + 1), j + 1];
      if (s[j] === '/' && j + 1 < n && s[j + 1] === '>') return [s.slice(i, j + 2), j + 2];
      // An attribute name must be preceded by whitespace.
      if (j === wsStart) return null;
      const ac = s.charCodeAt(j);
      if (!isAsciiLetter(ac) && ac !== 95 && ac !== 58) return null;
      while (j < n) {
        const cc = s.charCodeAt(j);
        if (isAsciiLetter(cc) || (cc >= 48 && cc <= 57) || cc === 45 || cc === 95 || cc === 58 || cc === 46) j++;
        else break;
      }
      // Look for '=' after optional whitespace, but do NOT consume the
      // whitespace if there is no '=' (it separates this attr from the next).
      let k = j;
      while (k < n && (s[k] === ' ' || s[k] === '\t' || s[k] === '\n')) k++;
      if (k < n && s[k] === '=') {
        j = k + 1;
        while (j < n && (s[j] === ' ' || s[j] === '\t' || s[j] === '\n')) j++;
        if (j >= n) return null;
        if (s[j] === '"') {
          j++;
          while (j < n && s[j] !== '"') j++;
          if (j >= n) return null;
          j++;
        } else if (s[j] === "'") {
          j++;
          while (j < n && s[j] !== "'") j++;
          if (j >= n) return null;
          j++;
        } else {
          const start = j;
          while (j < n) {
            const cc = s.charCodeAt(j);
            if (cc === 32 || cc === 9 || cc === 10 || cc === 34 || cc === 39 || cc === 61 || cc === 60 || cc === 62 || cc === 96) break;
            j++;
          }
          if (j === start) return null;
        }
      }
    }
  }
  return null;
}

function parseAngleAutolink(s, i) {
  const n = s.length;
  let j = i + 1;
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === 62) break;
    if (c === 60 || c === 32 || c === 9 || c === 10) return null;
    j++;
  }
  if (j >= n || s[j] !== '>') return null;
  const content = s.slice(i + 1, j);
  if (content.length === 0) return null;
  const colon = content.indexOf(':');
  if (colon >= 2 && colon <= 32) {
    let ok = isAsciiLetter(content.charCodeAt(0));
    for (let k = 1; ok && k < colon; k++) {
      const cc = content.charCodeAt(k);
      ok = isAsciiLetter(cc) || (cc >= 48 && cc <= 57) || cc === 43 || cc === 46 || cc === 45;
    }
    if (ok) return [content, content, j + 1];
  }
  const at = content.indexOf('@');
  if (at > 0) {
    let ok = true;
    for (let k = 0; k < at; k++) {
      if (!isAngleEmailLocal(content.charCodeAt(k))) { ok = false; break; }
    }
    if (ok) {
      const domEnd = matchEmailDomain(content, at + 1);
      if (domEnd === content.length) return ['mailto:' + content, content, j + 1];
    }
  }
  return null;
}

// Parse a link title starting at i ('"', "'", or '(').
// Returns [title, endIndex] or null.
function parseTitle(s, i) {
  const n = s.length;
  const q = s[i];
  if (q === '(') {
    let j = i + 1;
    while (j < n && s[j] !== '(' && s[j] !== ')') j++;
    if (j < n && s[j] === '(') {
      j++;
      while (j < n && s[j] !== '(' && s[j] !== ')') j++;
      if (j >= n || s[j] !== ')') return null;
      j++;
      if (j >= n || s[j] !== ')') return null;
      return [unescapeInline(s.slice(i + 1, j - 1)), j + 1];
    }
    if (j >= n || s[j] !== ')') return null;
    return [unescapeInline(s.slice(i + 1, j)), j + 1];
  }
  let j = i + 1;
  while (j < n) {
    if (s[j] === '\\' && j + 1 < n) { j += 2; continue; }
    if (s[j] === q) return [unescapeInline(s.slice(i + 1, j)), j + 1];
    j++;
  }
  return null;
}

function parseBareDest(s, i) {
  const n = s.length;
  let depth = 0;
  let j = i;
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === 32 || c === 9 || c === 10) break;
    if (c === 92 && j + 1 < n && isPunctCode(s.charCodeAt(j + 1))) { j += 2; continue; }
    if (c === 40) { depth++; j++; continue; }
    if (c === 41) {
      if (depth === 0) break;
      depth--;
      j++;
      continue;
    }
    j++;
  }
  if (depth !== 0) return null;
  if (j === i) return ['', i];
  return [unescapeInline(s.slice(i, j)), j];
}

function skipLinkWs(s, i) {
  const n = s.length;
  while (i < n && (s[i] === ' ' || s[i] === '\t' || s[i] === '\n')) i++;
  return i;
}

// After a destination: optional title + ')'. Returns {title, end} or null.
function parseLinkRest(s, i) {
  const n = s.length;
  const j = skipLinkWs(s, i);
  const hadWs = j > i;
  let title = null;
  let k = j;
  if (k < n && (s[k] === '"' || s[k] === "'" || s[k] === '(')) {
    if (!hadWs) return null;
    const t = parseTitle(s, k);
    if (!t) return null;
    title = t[0];
    k = skipLinkWs(s, t[1]);
  }
  if (k >= n || s[k] !== ')') return null;
  return { title, end: k + 1 };
}

function parseInlineLinkTail(s, start) {
  const n = s.length;
  let i = skipLinkWs(s, start + 1);
  if (i >= n) return null;
  if (s[i] === '<') {
    // Scan for an unescaped '>'; a newline is never allowed in an angle dest.
    for (let gt = i + 1; gt < n; gt++) {
      if (s[gt] === '\\' && gt + 1 < n) { gt++; continue; }
      if (s[gt] !== '>') continue;
      const destRaw = s.slice(i + 1, gt);
      if (destRaw.indexOf('\n') !== -1) continue;
      let hasWs = false, hasAngle = false;
      for (let k = 0; k < destRaw.length; k++) {
        const cc = destRaw.charCodeAt(k);
        if (cc === 32 || cc === 9 || cc === 10) hasWs = true;
        else if (cc === 60 || cc === 62) hasAngle = true;
      }
      if (hasWs && hasAngle) continue;
      const rest = parseLinkRest(s, gt + 1);
      if (rest) return { href: unescapeInline(destRaw), title: rest.title, end: rest.end };
    }
    return null;
  }
  const bd = parseBareDest(s, i);
  if (!bd) return null;
  const rest = parseLinkRest(s, bd[1]);
  if (!rest) return null;
  return { href: bd[0], title: rest.title, end: rest.end };
}

// Find the closing ']' of a ref label starting at i (just after '[').
// Skips backslash escapes; rejects unescaped '['. Returns index or -1.
function findLabelEnd(s, i) {
  const n = s.length;
  let j = i;
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === 92) { j += 2; continue; }
    if (c === 91) return -1;
    if (c === 93) return j;
    j++;
  }
  return -1;
}

function linkTextHasLink(items, open) {
  const idx = items.indexOf(open);
  for (let k = idx + 1; k < items.length; k++) {
    if (items[k].k === 2) return true;
  }
  return false;
}

// Marked's link tokenizer pairs backtick runs in the link text; an
// ODD number of unescaped backtick runs blocks an inline or full-ref
// link/image from forming — unless the link text ends with a backtick
// run that closes a code span (a matching run of the same length
// earlier: `[a \`\`b \` c\`\`](u)` links, but `[a \`b](u)` and
// `[foo\`](/uri)` do not). Escaped backticks (`\``) do not count.
// Shortcut refs are unaffected.
function linkTextHasOddBackticks(s, start, end) {
  let runs = 0;
  let lastLen = 0;
  let lastPos = -1;
  let p = start;
  while (p < end) {
    if (s.charCodeAt(p) === 96) {
      // Escaped if preceded by an odd run of backslashes.
      let bs = 0;
      let q = p - 1;
      while (q >= start && s.charCodeAt(q) === 92) { bs++; q--; }
      if (bs % 2 === 0) {
        runs++;
        const runStart = p;
        while (p < end && s.charCodeAt(p) === 96) p++;
        lastLen = p - runStart;
        lastPos = runStart;
        continue;
      }
    }
    p++;
  }
  if (runs % 2 === 0) return false;
  // A trailing run that closes a code span (matching opener earlier)
  // does not block.
  if (lastPos === -1 || lastPos + lastLen !== end) return true;
  for (let q = start; q < lastPos; q++) {
    if (s.charCodeAt(q) === 96) {
      let bs = 0;
      let r = q - 1;
      while (r >= start && s.charCodeAt(r) === 92) { bs++; r--; }
      if (bs % 2 === 0) {
        let len = 0;
        while (q + len < lastPos && s.charCodeAt(q + len) === 96) len++;
        if (len === lastLen) return false;
        q += len - 1;
      }
    }
  }
  return true;
}

function tryFormLink(s, i, items, open, refs) {
  const n = s.length;
  const after = i + 1 < n ? s.charCodeAt(i + 1) : -1;
  if (after === 40) { // (
    const parsed = parseInlineLinkTail(s, i + 1);
    if (parsed) {
      if (!open.image && linkTextHasLink(items, open)) return null;
      if (linkTextHasOddBackticks(s, open.textStart, i)) { open.backtickBlocked = true; return null; }
      return { open, href: parsed.href, title: parsed.title, end: parsed.end };
    }
    // Inline link failed to parse: fall through to shortcut ref.
  }
  if (after === 91) { // [
    const labelEnd = findLabelEnd(s, i + 2);
    if (labelEnd === -1) return null;
    let label;
    if (labelEnd === i + 2) label = s.slice(open.textStart, i);
    else label = s.slice(i + 2, labelEnd);
    const norm = normalizeLabel(label);
    if (norm === '') return null;
    const def = refs.get(norm);
    if (!def) return null;
    if (!open.image && linkTextHasLink(items, open)) return null;
    if (linkTextHasOddBackticks(s, open.textStart, i)) { open.backtickBlocked = true; return null; }
    return { open, href: def.href, title: def.title, end: labelEnd + 1 };
  }
  const label = s.slice(open.textStart, i);
  const norm = normalizeLabel(label);
  if (norm === '') return null;
  const def = refs.get(norm);
  if (!def) return null;
  if (!open.image && linkTextHasLink(items, open)) return null;
  return { open, href: def.href, title: def.title, end: i + 1 };
}

function resolveEmphasis(items) {
  const delims = [];
  for (const it of items) {
    if (it.k === 1 && (it.canOpen || it.canClose)) delims.push(it);
    else if (it.k === 2 || it.k === 3) resolveEmphasis(it.children);
  }
  // openersBottom[char]: a len-1 closer may only use openers above this
  // index. Set when a closer that can itself open pairs with an opener.
  const openersBottom = new Map();
  for (let ci = 0; ci < delims.length; ci++) {
    const closer = delims[ci];
    if (!closer.canClose || closer.len === 0 || !closer.active) continue;
    let oi = ci - 1;
    let sawOddBlock = false;
    let matched = false;
    // Snapshot openersBottom before this closer starts: a bottom set by
    // this closer's own match must not block its subsequent matches
    // (marked: `*a **b***` forms both the strong and the outer em).
    const bottom0 = closer.ch !== '~' ? (openersBottom.get(closer.ch) ?? -1) : -1;
    while (closer.len > 0 && oi >= 0) {
      // A len-1 closer respects openersBottom: nothing below it can match.
      if (closer.ch !== '~' && closer.len < 2) {
        if (oi <= bottom0) break;
      }
      const opener = delims[oi];
      if (!opener.active || opener.len === 0 || !opener.canOpen || opener.ch !== closer.ch) { oi--; continue; }
      // A len-2 closer can form a strong match below openersBottom, but
      // not an em match (marked: `**a *b **c** d* e**` matches the
      // outer `**` pair, leaving the inner `*` literal).
      if (closer.ch !== '~' && closer.len >= 2) {
        if (oi <= bottom0 && opener.len < 2) { oi--; continue; }
      }
      if (closer.ch === '~' && opener.len !== closer.len) { oi--; continue; }
      if (closer.ch !== '~') {
        const eitherBoth = (opener.canOpen && opener.canClose) || (closer.canOpen && closer.canClose);
        if (eitherBoth && (opener.len + closer.len) % 3 === 0 &&
            (opener.len % 3 !== 0 || closer.len % 3 !== 0)) { sawOddBlock = true; oi--; continue; }
        // An opener that itself failed as a closer (odd-match) can only
        // be used by a closer that can open, or one that still has
        // delimiters left after the match (marked: `*foo**bar** baz*`
        // matches the outer `*`, but `*foo**bar***` forms strong).
        // Only strong matches are blocked; an em match on an oddFailed
        // opener is fine (marked: `**a *b* c**` forms the inner em).
        if (opener.oddFailed && !closer.canOpen) {
          const n2 = (opener.len >= 2 && closer.len >= 2) ? 2 : 1;
          if (n2 === 2 && closer.len <= n2) { oi--; continue; }
        }
      }
      let n, tag;
      if (closer.ch === '~') { n = opener.len; tag = 'del'; }
      else if (opener.len >= 2 && closer.len >= 2) { n = 2; tag = 'strong'; }
      else { n = 1; tag = 'em'; }
      opener.uo.push(tag);
      closer.uc.push(tag);
      opener.len -= n;
      closer.len -= n;
      matched = true;
      for (let d = oi + 1; d < ci; d++) {
        // A same-char delimiter left unmatched between opener and closer
        // pulls this closer's leftover chars inside the emphasis
        // (marked: `*foo**bar**` -> `<em>foo**bar*</em>`, but `*foo**`
        // -> `<em>foo</em>*`). A strong match also pulls the leftover
        // inside when a matched <em> pair sits between (marked:
        // `**a *b* c***` -> `<strong>a <em>b</em> c*</strong>`, but
        // `*a *b* c**` -> `<em>a <em>b</em> c</em>*` and `**foo***` ->
        // `<strong>foo</strong>*`).
        if (delims[d].ch === closer.ch &&
            (delims[d].len > 0 ||
             (n === 2 && (delims[d].uo.includes('em') || delims[d].uc.includes('em'))))) {
          closer.leftoverInside = true;
        }
        delims[d].active = false;
      }
      // openersBottom is set when a closer that can itself open pairs with
      // an opener that cannot close. For a strong match, always; for an
      // em match, only when an earlier unmatched opener of the same char
      // has length >= 2 (so a later strong closer can still use it:
      // `**a *b* c**` forms strong, but `*a *b* c*` forms the outer em).
      if (closer.canOpen && closer.ch !== '~' && !opener.canClose) {
        let setBottom = n === 2;
        if (!setBottom) {
          for (let b = oi - 1; b >= 0; b--) {
            const prev = delims[b];
            if (prev.ch !== closer.ch || !prev.active || prev.len === 0 || !prev.canOpen) continue;
            if (prev.len >= 2) { setBottom = true; break; }
          }
        }
        if (setBottom) openersBottom.set(closer.ch, oi);
      }
      if (opener.len === 0) oi--;
    }
    // A closer that matched nothing and was blocked by the odd-match rule
    // is marked: later closers may only use it as an opener under the
    // conditions above.
    if (!matched && sawOddBlock) closer.oddFailed = true;
  }
}

// Convert BARE autolink items (kind 6, no angle flag) in `children` back to
// plain text items. Used when a link forms: bare autolinks do not form
// inside link text, but <...> angle autolinks DO nest (marked renders them
// as nested <a> elements), so angle autolinks are left alone.
function suppressAutolinks(children) {
  for (let i = 0; i < children.length; i++) {
    const it = children[i];
    if (it.k === 6 && !it.angle) children[i] = { k: 0, s: it.text };
    else if (it.k === 3) suppressAutolinks(it.children);
  }
}

function resolveEmails(items, inLinkStart) {
  // Note: no recursion into link/image children — emails do not form
  // inside link text (and image children are plain alt text).
  // inLink is re-derived per text run from the state at the start of
  // this inline parse, so an email before an <a> tag in the same
  // paragraph still links, while one after it (or in a later block,
  // once the cross-block state is set) does not.
  let inLink = inLinkStart;
  const out = [];
  let i = 0;
  while (i < items.length) {
    const it = items[i];
    if (it.k === 5) {
      const ls = htmlLinkState(it.s);
      if (ls !== null) inLink = ls;
      out.push(it); i++; continue;
    }
    const textLike = (it.k === 0 && !it.esc) || (it.k === 1 && it.uo.length === 0 && it.uc.length === 0 && it.len > 0);
    if (!textLike) { out.push(it); i++; continue; }
    // Collect a maximal run of text-like items, keeping the original
    // boundaries: merging must not let an entity form across a boundary
    // (e.g. an escaped '&' followed by 'ouml;'), and an escaped char is
    // a barrier for email local-part scanning.
    const run = [];
    let merged = '';
    while (i < items.length) {
      const it2 = items[i];
      const tl = (it2.k === 0 && !it2.esc) || (it2.k === 1 && it2.uo.length === 0 && it2.uc.length === 0 && it2.len > 0);
      if (!tl) break;
      const str = it2.k === 0 ? it2.s : it2.ch.repeat(it2.len);
      run.push({ start: merged.length, str, item: it2 });
      merged += str;
      i++;
    }
    if (merged.indexOf('@') === -1 || inLink) {
      for (let r = 0; r < run.length; r++) out.push(run[r].item);
      continue;
    }
    // Scan for emails in the merged view; emit non-email spans from the
    // ORIGINAL items so entity boundaries are preserved.
    let scanPos = 0;
    let emitPos = 0;
    while (true) {
      const at = merged.indexOf('@', scanPos);
      if (at === -1) break;
      let ls = at - 1;
      while (ls >= emitPos && isEmailLocalChar(merged.charCodeAt(ls))) ls--;
      ls++;
      if (ls === at) { scanPos = at + 1; continue; }
      const domEnd = matchEmailDomain(merged, at + 1);
      if (domEnd === -1) { scanPos = at + 1; continue; }
      if (ls > emitPos) emitOriginalText(out, run, emitPos, ls);
      out.push({ k: 9, addr: merged.slice(ls, domEnd) });
      emitPos = domEnd;
      scanPos = domEnd;
    }
    if (emitPos < merged.length) emitOriginalText(out, run, emitPos, merged.length);
  }
  items.length = 0;
  for (const it of out) items.push(it);
}

function emitOriginalText(out, run, from, to) {
  for (let r = 0; r < run.length; r++) {
    const seg = run[r];
    const rs = seg.start;
    const re = rs + seg.str.length;
    if (re <= from || rs >= to) continue;
    const part = seg.str.slice(Math.max(from, rs) - rs, Math.min(to, re) - rs);
    if (part.length > 0) out.push({ k: 0, s: part });
  }
}

function plainText(items) {
  let out = '';
  for (const it of items) {
    switch (it.k) {
      case 0: out += it.s; break;
      case 1: if (it.len > 0) out += it.ch.repeat(it.len); break;
      case 2: case 3: out += plainText(it.children); break;
      case 4: out += it.s; break;
      case 6: out += it.text; break;
      case 8: out += it.image ? '![' : '['; break;
      case 9: out += it.addr; break;
      default: break;
    }
  }
  return out;
}

function renderInline(items) {
  let out = '';
  for (const it of items) {
    switch (it.k) {
      case 0:
        out += escapeText(it.s);
        break;
      case 1: {
        // Leftover delimiter chars render before the closing tags only
        // when an unmatched same-char delimiter sits between opener and
        // closer (see resolveEmphasis); otherwise after them.
        if (it.leftoverInside && it.len > 0) out += it.ch.repeat(it.len);
        for (const tag of it.uc) out += tag === 'em' ? '</em>' : tag === 'strong' ? '</strong>' : '</del>';
        if (!it.leftoverInside && it.len > 0) out += it.ch.repeat(it.len);
        for (let u = it.uo.length - 1; u >= 0; u--) {
          const tag = it.uo[u];
          out += tag === 'em' ? '<em>' : tag === 'strong' ? '<strong>' : '<del>';
        }
        break;
      }
      case 2: {
        const href = cleanUrl(it.href);
        if (href === null) { out += renderInline(it.children); break; }
        out += '<a href="' + escapeHref(href) + '"';
        if (it.title !== null && it.title !== undefined) out += ' title="' + escapeHref(it.title) + '"';
        out += '>' + renderInline(it.children) + '</a>';
        break;
      }
      case 3: {
        const href = cleanUrl(it.href);
        const alt = plainText(it.children);
        if (href === null) { out += escapeText(alt); break; }
        out += '<img src="' + escapeHref(href) + '" alt="' + escapeText(alt) + '"';
        if (it.title !== null && it.title !== undefined) out += ' title="' + escapeHref(it.title) + '"';
        out += '>';
        break;
      }
      case 4:
        out += '<code>' + escapeUncond(it.s) + '</code>';
        break;
      case 5:
        out += it.s;
        break;
      case 6: {
        const href = cleanUrl(it.href);
        if (href === null) { out += escapeUncond(it.text); break; }
        out += '<a href="' + escapeUncond(href) + '">' + escapeUncond(it.text) + '</a>';
        break;
      }
      case 7:
        out += '<br>';
        break;
      case 8:
        out += it.image ? '![' : '[';
        break;
      case 9:
        out += '<a href="mailto:' + escapeUncond(it.addr) + '">' + escapeUncond(it.addr) + '</a>';
        break;
    }
  }
  return out;
}

// Special chars for the parseInline scan: structural chars plus the
// letters that can start a bare autolink (w/h/H/f/F/m/x). The regex jump
// skips plain-text runs far faster than a char-by-char loop.
const INLINE_SPECIAL_RE = /[\\\n`*_~\[\]!<>whHfFmx]/g;

function parseInline(s, refs) {
  const items = [];
  const opens = [];
  let textStart = 0;
  const n = s.length;
  // Snapshot the cross-block inLink state: resolveEmails re-derives the
  // per-position state from this (the main scan updates the global as
  // it goes, so by the time emails resolve the global is the END state).
  const inLinkStart = inLinkGlobal;
  const flush = (upTo) => { if (upTo > textStart) items.push({ k: 0, s: s.slice(textStart, upTo) }); };
  let i = 0;
  INLINE_SPECIAL_RE.lastIndex = 0;
  while (i < n) {
    INLINE_SPECIAL_RE.lastIndex = i;
    const m = INLINE_SPECIAL_RE.exec(s);
    if (!m) break;
    i = m.index;
    const c = s.charCodeAt(i);
    if (c === 92) { // backslash
      if (i + 1 < n) {
        const nc = s.charCodeAt(i + 1);
        if (nc === 10) {
          flush(i);
          items.push({ k: 7 });
          i += 2;
          while (i < n && (s.charCodeAt(i) === 32 || s.charCodeAt(i) === 9)) i++;
          textStart = i;
          continue;
        }
        if (nc < 128 && ASCII_PUNCT[nc]) {
          flush(i);
          items.push({ k: 0, s: s[i + 1], esc: true });
          i += 2;
          textStart = i;
          continue;
        }
      }
      i++;
      continue;
    }
    if (c === 10) { // newline: hard break if 2+ trailing spaces in the run
      let j = i - 1;
      let spaces = 0;
      while (j >= textStart && s.charCodeAt(j) === 32) { spaces++; j--; }
      if (spaces >= 2) {
        flush(i - spaces);
        items.push({ k: 7 });
        i++;
        while (i < n && (s.charCodeAt(i) === 32 || s.charCodeAt(i) === 9)) i++;
        textStart = i;
      } else {
        i++;
      }
      continue;
    }
    if (c === 96) { // backtick
      const cs = parseCodeSpan(s, i);
      if (cs) {
        // Marked matches a link before a code span: a code span must not
        // swallow a `]` that closes an open bracket and forms a link
        // (marked: `[a \`b\` c](#u) [d \`e\`](#v)` forms both links, not
        // a code span from the first `` ` `` to the third). If the `]`
        // would not form a link (e.g. odd backtick parity, cm-525), the
        // code span wins.
        let blocked = false;
        if (opens.length > 0) {
          let j = s.indexOf(']', i + 1);
          while (j !== -1 && j < cs[1]) {
            if (tryFormLink(s, j, items, opens[opens.length - 1], refs)) { blocked = true; break; }
            j = s.indexOf(']', j + 1);
          }
        }
        if (!blocked) {
          flush(i);
          items.push({ k: 4, s: cs[0] });
          i = cs[1];
          textStart = i;
          continue;
        }
      }
      // No matching closer: the whole run is literal text.
      let j = i + 1;
      while (j < n && s.charCodeAt(j) === 96) j++;
      i = j;
      continue;
    }
    if (c === 42 || c === 95 || c === 126) { // * _ ~
      const ch = s[i];
      let j = i;
      while (j < n && s.charCodeAt(j) === c) j++;
      const len = j - i;
      if (ch === '~' && len >= 3) { i = j; continue; }
      const fl = flanking(s, i, len);
      let canOpen, canClose;
      if (ch === '_') {
        canOpen = fl.left && (!fl.right || fl.beforePunct);
        canClose = fl.right && (!fl.left || fl.afterPunct);
      } else {
        canOpen = fl.left;
        canClose = fl.right;
      }
      flush(i);
      items.push({ k: 1, ch, len, orig: len, canOpen, canClose, active: true, uo: [], uc: [] });
      i = j;
      textStart = i;
      continue;
    }
    if (c === 33) { // !
      if (i + 1 < n && s.charCodeAt(i + 1) === 91) {
        flush(i);
        const open = { k: 8, image: true, textStart: i + 2 };
        items.push(open);
        opens.push(open);
        i += 2;
        textStart = i;
        continue;
      }
      i++;
      continue;
    }
    if (c === 91) { // [
      flush(i);
      const open = { k: 8, image: false, textStart: i + 1 };
      items.push(open);
      opens.push(open);
      i++;
      textStart = i;
      continue;
    }
    if (c === 93) { // ]
      if (opens.length > 0) {
        const open = opens[opens.length - 1];
        const link = tryFormLink(s, i, items, open, refs);
        if (link) {
          flush(i);
          const openIdx = items.indexOf(link.open);
          const children = items.splice(openIdx + 1);
          items.splice(openIdx, 1);
          opens.pop();
          // Autolinks do not form inside link text: turn them back into
          // plain text (the outer link still forms).
          if (!link.open.image) suppressAutolinks(children);
          items.push({ k: link.open.image ? 3 : 2, href: link.href, title: link.title, children });
          i = link.end;
          textStart = i;
          continue;
        }
        // A link blocked by odd backtick parity also kills emphasis
        // inside its text — but only when a code span in the text
        // contains a backtick itself (marked: `[a _b \`\`c \` d\`\`_ e](u)`
        // leaves the `_` literal, but `[a _b \`c \` d\`_ e](u)` forms
        // the em).
        if (open.backtickBlocked) {
          const openIdx = items.indexOf(open);
          let nestedTick = false;
          for (let k = openIdx + 1; k < items.length; k++) {
            if (items[k].k === 4 && items[k].s.indexOf('`') !== -1) { nestedTick = true; break; }
          }
          if (nestedTick) {
            for (let k = openIdx + 1; k < items.length; k++) {
              if (items[k].k === 1) items[k].active = false;
            }
          }
        }
        // This opener cannot form a link here; deactivate it so a later
        // ']' tries an outer opener.
        opens.pop();
      }
      i++;
      continue;
    }
    if (c === 60) { // <
      const html = parseInlineHtml(s, i);
      if (html) {
        flush(i);
        items.push({ k: 5, s: html[0] });
        const ls = htmlLinkState(html[0]);
        if (ls !== null) inLinkGlobal = ls;
        i = html[1];
        textStart = i;
        continue;
      }
      const al = parseAngleAutolink(s, i);
      if (al) {
        flush(i);
        items.push({ k: 6, href: al[0], text: al[1], angle: true });
        i = al[2];
        textStart = i;
        continue;
      }
      i++;
      continue;
    }
    if (c === 119 || c === 104 || c === 72 || c === 102 || c === 70 || c === 109 || c === 120) {
      // Inside an unclosed <a> (cross-block state), bare autolinks do
      // not form (angle autolinks still do; see the '<' branch above).
      if (inLinkGlobal) { i++; continue; }
      let al = matchAutolink(s, i);
      if (al && opens.length > 0) {
        // A bare autolink must not swallow a `]` that closes an open
        // bracket and forms a link there: the link wins (marked's link
        // tokenizer runs before its autolink tokenizer). Simulate the
        // `]` handler over each `]` in the autolink's span, in order: a
        // `]` that forms a link truncates the autolink there; one that
        // does not pops its opener (as the real handler would) and the
        // scan continues with the next opener out.
        let depth = opens.length;
        let limit = -1;
        let pops = 0;
        let j = s.indexOf(']', i + 1);
        while (j !== -1 && j < al[2] && depth > 0) {
          if (tryFormLink(s, j, items, opens[depth - 1], refs)) { limit = j; break; }
          depth--;
          pops++;
          j = s.indexOf(']', j + 1);
        }
        if (limit !== -1) {
          // Pop the openers the earlier `]`s would have popped, so the
          // link forms with the right opener when the parser reaches it.
          while (pops-- > 0) opens.pop();
          const al2 = matchAutolink(s, i, limit);
          if (al2) al = al2;
          else {
            // The truncated span is not an autolink after all: treat
            // this char as plain text (the `]` will form the link).
            i++;
            continue;
          }
        }
      }
      if (al) {
        flush(i);
        items.push({ k: 6, href: al[0], text: al[1] });
        i = al[2];
        textStart = i;
        continue;
      }
      i++;
      continue;
    }
    i++;
  }
  flush(n);
  // A link whose text holds unmatched backticks, followed later by code
  // spans, kills emphasis between the link and the LAST such code span
  // (marked: `[a \`\`b\` c](u) *d* \`f\` *h* \`j\`` leaves both `*d*`
  // and `*h*` literal, but without the trailing `` `j` `` the `*h*`
  // forms — the stray backtick pairs with the last backtick).
  // The code span may sit inside a later link's text.
  const hasCodeSpan = (item) => {
    if (item.k === 4) return true;
    if ((item.k === 2 || item.k === 3) && item.children) {
      return item.children.some(hasCodeSpan);
    }
    return false;
  };
  for (let li = 0; li < items.length; li++) {
    const it = items[li];
    if ((it.k !== 2 && it.k !== 3) || !it.children) continue;
    let strayTick = false;
    for (const ch of it.children) {
      if (ch.k === 0 && !ch.esc && ch.s.indexOf('`') !== -1) { strayTick = true; break; }
    }
    if (!strayTick) continue;
    let lastCs = -1;
    for (let ci = li + 1; ci < items.length; ci++) {
      if (hasCodeSpan(items[ci])) lastCs = ci;
    }
    if (lastCs !== -1) {
      for (let d = li + 1; d < lastCs; d++) {
        if (items[d].k === 1) items[d].active = false;
      }
    }
  }
  resolveEmphasis(items);
  resolveEmails(items, inLinkStart);
  return renderInline(items);
}

// ---------------------------------------------------------------------------
// Block parsing helpers
// ---------------------------------------------------------------------------

class LineCursor {
  constructor(s) {
    this.s = s;
    this.i = 0;
    this.col = 0;
    this.spaces = 0; // virtual spaces from a partially consumed tab
  }

  save() { return [this.i, this.col, this.spaces]; }
  restore(st) { this.i = st[0]; this.col = st[1]; this.spaces = st[2]; }

  cur() {
    if (this.spaces > 0) return 32;
    if (this.i >= this.s.length) return -1;
    return this.s.charCodeAt(this.i);
  }

  // Advance past the current character (a tab jumps to the next stop).
  advance() {
    if (this.spaces > 0) { this.spaces--; this.col++; return; }
    if (this.i >= this.s.length) return;
    if (this.s.charCodeAt(this.i) === 9) {
      this.col += 4 - (this.col % 4);
      this.i++;
    } else {
      this.col++;
      this.i++;
    }
  }

  // Consume exactly one column (a tab leaves virtual spaces behind).
  consumeOneColumn() {
    if (this.spaces > 0) { this.spaces--; this.col++; return; }
    if (this.i >= this.s.length) return;
    if (this.s.charCodeAt(this.i) === 9) {
      const toNext = 4 - (this.col % 4);
      this.spaces = toNext - 1;
      this.i++;
      this.col++;
    } else {
      this.i++;
      this.col++;
    }
  }

  // Skip up to n columns of indent. Returns columns actually skipped.
  skipIndent(n) {
    let skipped = 0;
    while (skipped < n) {
      if (this.spaces > 0) {
        const take = Math.min(this.spaces, n - skipped);
        this.spaces -= take;
        this.col += take;
        skipped += take;
      } else if (this.i < this.s.length && this.s.charCodeAt(this.i) === 32) {
        this.i++; this.col++; skipped++;
      } else if (this.i < this.s.length && this.s.charCodeAt(this.i) === 9) {
        const toNext = 4 - (this.col % 4);
        if (skipped + toNext <= n) {
          this.i++; this.col += toNext; skipped += toNext;
        } else {
          const take = n - skipped;
          this.spaces = toNext - take;
          this.i++; this.col += take; skipped += take;
        }
      } else break;
    }
    return skipped;
  }

  // Skip up to n leading whitespace CHARACTERS (a tab counts as 1 and is
  // removed entirely). Used for fenced-code content indent.
  skipFenceIndent(n) {
    let skipped = 0;
    while (skipped < n) {
      if (this.spaces > 0) {
        const take = Math.min(this.spaces, n - skipped);
        this.spaces -= take;
        this.col += take;
        skipped += take;
      } else if (this.i < this.s.length && this.s.charCodeAt(this.i) === 32) {
        this.i++; this.col++; skipped++;
      } else if (this.i < this.s.length && this.s.charCodeAt(this.i) === 9) {
        this.col += 4 - (this.col % 4);
        this.i++;
        skipped++;
      } else break;
    }
    return skipped;
  }

  // Columns of indent available at the current position (spaces/tabs).
  indentAvailable() {
    let col = this.col;
    let i = this.i;
    let spaces = this.spaces;
    let count = 0;
    while (true) {
      if (spaces > 0) { count += spaces; col += spaces; spaces = 0; }
      else if (i < this.s.length && this.s.charCodeAt(i) === 32) { i++; col++; count++; }
      else if (i < this.s.length && this.s.charCodeAt(i) === 9) {
        const toNext = 4 - (col % 4);
        col += toNext; count += toNext; i++;
      } else break;
    }
    return count;
  }

  // Measure the whitespace run at the current position.
  measureWhitespace() {
    let col = this.col;
    let i = this.i;
    let spaces = this.spaces;
    let columns = 0;
    while (true) {
      if (spaces > 0) { columns += spaces; col += spaces; spaces = 0; }
      else if (i < this.s.length && this.s.charCodeAt(i) === 32) { i++; col++; columns++; }
      else if (i < this.s.length && this.s.charCodeAt(i) === 9) {
        const toNext = 4 - (col % 4);
        col += toNext; columns += toNext; i++;
      } else break;
    }
    return { columns, endCol: col, blank: i >= this.s.length };
  }

  rest() {
    if (this.spaces > 0) return ' '.repeat(this.spaces) + this.s.slice(this.i);
    return this.s.slice(this.i);
  }

  isBlank() {
    for (let j = this.i; j < this.s.length; j++) {
      const c = this.s.charCodeAt(j);
      if (c !== 32 && c !== 9) return false;
    }
    return true;
  }
}

// HTML block tag list (CommonMark type 6).
const BLOCK_TAGS = new Set([
  'address', 'article', 'aside', 'base', 'basefont', 'blockquote', 'body',
  'caption', 'center', 'col', 'colgroup', 'dd', 'details', 'dialog', 'dir',
  'div', 'dl', 'dt', 'fieldset', 'figcaption', 'figure', 'footer', 'form',
  'frame', 'frameset', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'head', 'header',
  'hr', 'html', 'iframe', 'legend', 'li', 'link', 'main', 'menu', 'menuitem',
  'meta', 'nav', 'noframes', 'ol', 'optgroup', 'option', 'p', 'param',
  'search', 'section', 'summary', 'table', 'tbody', 'td', 'tfoot', 'th',
  'thead', 'title', 'tr', 'track', 'ul',
]);

// Determine the HTML block type for a line whose content (after container
// prefixes and up to 3 spaces of indent) is `rest`.
// Returns {type, end} where end is the end-marker string for types 1-5
// (null for 6-7), or null if this is not an HTML block start.
function htmlBlockType(rest) {
  if (rest.length === 0 || rest.charCodeAt(0) !== 60) return null;
  const lower = rest.slice(0, 12).toLowerCase();
  // Type 1: pre, script, style, textarea
  for (const tag of ['pre', 'script', 'style', 'textarea']) {
    if (lower.startsWith('<' + tag)) {
      const after = rest.charCodeAt(1 + tag.length);
      if (Number.isNaN(after) || after === 32 || after === 9 || after === 62 || after === 10) {
        return { type: 1, end: '</' + tag };
      }
    }
  }
  if (rest.startsWith('<!--')) return { type: 2, end: '-->' };
  if (rest.startsWith('<?')) return { type: 3, end: '?>' };
  if (rest.startsWith('<![CDATA[')) return { type: 5, end: ']]>' };
  if (rest.length > 2 && rest.charCodeAt(1) === 33 && isAsciiLetter(rest.charCodeAt(2))) {
    return { type: 4, end: '>' };
  }
  // Type 6: block tag open/close at line start.
  let j = 1;
  let closing = false;
  if (rest.charCodeAt(j) === 47) { closing = true; j++; }
  let k = j;
  while (k < rest.length && isAsciiLetter(rest.charCodeAt(k))) k++;
  if (k > j) {
    const name = rest.slice(j, k).toLowerCase();
    const after = k < rest.length ? rest.charCodeAt(k) : -1;
    if (BLOCK_TAGS.has(name) && (after === -1 || after === 32 || after === 9 || after === 62 || after === 47)) {
      return { type: 6, end: null };
    }
  }
  // Type 7: a complete open or close tag alone on the line.
  if (!closing) {
    const html = parseInlineHtml(rest, 0);
    if (html && html[1] === rest.length) return { type: 7, end: null };
    // Trailing whitespace allowed after the tag.
    if (html) {
      let m = html[1];
      let onlyWs = true;
      while (m < rest.length) {
        const c = rest.charCodeAt(m);
        if (c !== 32 && c !== 9) { onlyWs = false; break; }
        m++;
      }
      if (onlyWs) return { type: 7, end: null };
    }
  } else {
    const html = parseInlineHtml(rest, 0);
    if (html) {
      let m = html[1];
      let onlyWs = true;
      while (m < rest.length) {
        const c = rest.charCodeAt(m);
        if (c !== 32 && c !== 9) { onlyWs = false; break; }
        m++;
      }
      if (onlyWs) return { type: 7, end: null };
    }
  }
  return null;
}

// Split a table row line into cells. Handles \| (odd backslash runs).
function splitTableRow(line) {
  const cells = [];
  let cur = '';
  let backslashes = 0;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (c === '\\') { backslashes++; cur += c; continue; }
    if (c === '|') {
      if (backslashes % 2 === 1) {
        // Escaped pipe: drop the backslash, keep the literal pipe.
        cur = cur.slice(0, -1) + c;
        backslashes = 0;
        continue;
      }
      cells.push(cur);
      cur = '';
      backslashes = 0;
      continue;
    }
    backslashes = 0;
    cur += c;
  }
  cells.push(cur);
  const trimmed = line.trim();
  if (cells.length > 1 && trimmed.charCodeAt(0) === 124) cells.shift();
  if (cells.length > 1 && trimmed.charCodeAt(trimmed.length - 1) === 124) cells.pop();
  for (let i = 0; i < cells.length; i++) cells[i] = cells[i].trim();
  return cells;
}

// Parse a delimiter row. Returns the alignment array or null.
function parseDelimiterRow(line) {
  const cells = splitTableRow(line);
  if (cells.length === 0) return null;
  const align = [];
  for (const cell of cells) {
    let c = cell;
    let left = false, right = false;
    if (c.charCodeAt(0) === 58) { left = true; c = c.slice(1); }
    if (c.length > 0 && c.charCodeAt(c.length - 1) === 58) { right = true; c = c.slice(0, -1); }
    if (c.length === 0) return null;
    for (let i = 0; i < c.length; i++) {
      if (c.charCodeAt(i) !== 45) return null;
    }
    align.push(left && right ? 'center' : left ? 'left' : right ? 'right' : null);
  }
  return align;
}

// Parse one link reference definition starting at `pos` in `content`
// (which is a paragraph's joined lines; pos is at a line start).
// Returns {label, href, title, endPos} or null.
function parseLinkRefDef(content, pos) {
  const n = content.length;
  let i = pos;
  // Up to 3 spaces of indent.
  let indent = 0;
  while (i < n && indent < 3) {
    const c = content.charCodeAt(i);
    if (c === 32) { indent++; i++; }
    else if (c === 9) {
      const toNext = 4 - (indent % 4);
      if (indent + toNext > 3) break;
      indent += toNext; i++;
    } else break;
  }
  if (i >= n || content.charCodeAt(i) !== 91) return null; // [
  // Label: no unescaped [ or ], non-empty.
  let j = i + 1;
  let labelEnd = -1;
  while (j < n) {
    const c = content.charCodeAt(j);
    if (c === 92) { j += 2; continue; }
    if (c === 91) return null;
    if (c === 93) { labelEnd = j; break; }
    j++;
  }
  if (labelEnd === -1 || labelEnd === i + 1) return null;
  const label = content.slice(i + 1, labelEnd);
  if (normalizeLabel(label) === '') return null; // whitespace-only label
  j = labelEnd + 1;
  if (j >= n || content.charCodeAt(j) !== 58) return null; // :
  j++;
  // Skip whitespace (spaces, tabs, newlines) — dest may be on next line.
  j = skipLinkWs(content, j);
  if (j >= n) return null;
  let href;
  if (content.charCodeAt(j) === 60) { // < angle dest
    const gt = content.indexOf('>', j + 1);
    if (gt === -1) return null;
    const destRaw = content.slice(j + 1, gt);
    // No newline in an angle dest; no < or > inside (def form is strict).
    if (destRaw.indexOf('\n') !== -1 || destRaw.indexOf('<') !== -1 || destRaw.indexOf('>') !== -1) return null;
    href = unescapeInline(destRaw);
    j = gt + 1;
  } else {
    const bd = parseBareDest(content, j);
    if (!bd || bd[1] === j) return null;
    href = bd[0];
    j = bd[1];
  }
  // After the dest: optional title (same line or next line), then the
  // line must end. If the following text is not a title, the def still
  // succeeds without one and the rest stays paragraph content.
  const k = skipLinkWs(content, j);
  let title = null;
  let endPos = -1;
  if (k < n && (content[k] === '"' || content[k] === "'" || content[k] === '(')) {
    // A title requires whitespace between it and the destination.
    if (k === j) return null;
    // Title: paren form allows NO nesting in definitions.
    let t = null;
    if (content[k] === '(') {
      let m = k + 1;
      while (m < n && content[m] !== '(' && content[m] !== ')') m++;
      if (m < n && content[m] === ')') t = [unescapeInline(content.slice(k + 1, m)), m + 1];
    } else {
      t = parseTitle(content, k);
    }
    if (!t) return null; // title-like text that is not a valid title
    title = t[0];
    let m = t[1];
    while (m < n && (content[m] === ' ' || content[m] === '\t')) m++;
    if (m >= n) endPos = n;
    else if (content[m] === '\n') endPos = m + 1;
    else return null; // junk after title
  } else {
    // No title: the dest's own line must end after the dest.
    let m = j;
    while (m < n && (content[m] === ' ' || content[m] === '\t')) m++;
    if (m >= n) endPos = n;
    else if (content[m] === '\n') endPos = m + 1;
    else return null; // junk after dest
  }
  return { label, href, title, endPos };
}

// Dry-run def parsing (no storing): end position of the last consecutive
// def parsed from the start of content, or 0 if none.
function defsEndPos(content) {
  let pos = 0;
  while (true) {
    const def = parseLinkRefDef(content, pos);
    if (!def) break;
    pos = def.endPos;
  }
  return pos;
}

// ---------------------------------------------------------------------------
// Document parser: block structure
// ---------------------------------------------------------------------------

class DocParser {
  constructor(markdown) {
    let s = markdown;
    if (s.indexOf('\r') !== -1) s = s.replace(/\r\n?/g, '\n');
    this.endsWithNL = s.length > 0 && s.charCodeAt(s.length - 1) === 10;
    if (s === '') this.lines = [];
    else {
      this.lines = s.split('\n');
      if (this.endsWithNL) this.lines.pop();
    }
    this.refs = new Map();
    this.root = { t: 'doc', children: [] };
    this.stack = [this.root];
    this.leaf = null;
    this.htmlPending = null;
    this.tabBaseCol = 0;
    this.curLine = 0;
  }

  run() {
    for (let li = 0; li < this.lines.length; li++) {
      this.curLine = li;
      this.processLine(li);
    }
    this.curLine = this.lines.length;
    this.closeLeaf('eof');
    this.popTo(1);
    return renderBlocks(this.root.children, this.refs);
  }

  popTo(depth) {
    while (this.stack.length > depth) {
      const node = this.stack.pop();
      if (node.t === 'list') this.trimListTail(node);
    }
  }

  // Marked trims the trailing whitespace of a list's last line.
  trimListTail(list) {
    let node = list;
    while (true) {
      const children = node.children;
      if (!children || children.length === 0) return;
      const last = children[children.length - 1];
      if (last.t === 'item' || last.t === 'quote' || last.t === 'list') {
        node = last;
        continue;
      }
      if (last.t === 'para') {
        if (last.lines) {
          const lines = last.lines;
          if (lines.length > 0) lines[lines.length - 1] = stripTrailingWs(lines[lines.length - 1]);
        } else if (last.content !== null && last.content !== undefined) {
          last.content = stripTrailingWs(last.content);
        }
      } else if (last.t === 'code') {
        const lines = last.lines;
        if (lines && lines.length > 0) lines[lines.length - 1] = stripTrailingWs(lines[lines.length - 1]);
      } else if (last.t === 'fence') {
        if (!last.closed) {
          const lines = last.lines;
          if (lines && lines.length > 0) lines[lines.length - 1] = stripTrailingWs(lines[lines.length - 1]);
        }
      } else if (last.t === 'html') {
        const lines = last.lines;
        if (lines && lines.length > 0) lines[lines.length - 1] = stripTrailingWs(lines[lines.length - 1]);
      }
      return;
    }
  }

  processLine(li) {
    const line = this.lines[li];
    const cursor = new LineCursor(line);
    // Phase 1: match open containers top-down.
    let lastMatched = 0;
    // Tab-expansion base (quotes only): marked expands a leading tab in
    // content as if the line had only the innermost blockquote's prefix
    // (e.g. `> > \t` expands the tab to 2 spaces, not 4). Lists do not
    // get this treatment (a deeply nested list keeps the absolute column).
    let tabBaseCol = 0;
    let innermostIsQuote = false;
    let quoteNoSpace = false;
    for (let d = 1; d < this.stack.length; d++) {
      const container = this.stack[d];
      const saved = cursor.save();
      let ok = true;
      if (container.t === 'quote') {
        const colBeforeQuote = cursor.col;
        const colBefore = cursor.col;
        ok = this.matchBlockquote(cursor);
        if (ok) {
          tabBaseCol = colBeforeQuote;
          innermostIsQuote = true;
          // A `>` with no space after it still counts as a 2-column
          // prefix for tab expansion (marked: `>\t` -> 2 spaces).
          quoteNoSpace = cursor.col - colBefore < 2;
        }
      } else if (container.t === 'item') {
        ok = this.matchListItem(cursor, container);
        if (ok) innermostIsQuote = false;
      }
      if (!ok) { cursor.restore(saved); break; }
      lastMatched = d;
    }
    this.tabBaseCol = innermostIsQuote ? tabBaseCol - (quoteNoSpace ? 1 : 0) : 0;
    const allMatched = lastMatched === this.stack.length - 1;
    // Blankness: if all containers matched and the innermost one is a
    // blockquote, the line is blank only when nothing remains after the
    // marker (whitespace-only remainder is paragraph content); otherwise
    // a whitespace-only remainder is blank.
    let isBlank;
    if (allMatched) {
      let innermost = null;
      for (let d = lastMatched; d >= 1; d--) {
        const t = this.stack[d].t;
        if (t === 'quote' || t === 'item') { innermost = t; break; }
      }
      if (innermost === 'quote') isBlank = cursor.i >= cursor.s.length && cursor.spaces === 0;
      else isBlank = cursor.isBlank();
    } else {
      isBlank = cursor.isBlank();
    }
    // Inside a table, a line of 0-3 spaces plus exactly one tab is not
    // blank (marked treats it as an empty row); any other whitespace-only
    // line still ends the table. The tab line must be a complete line
    // (followed by a newline), not trailing whitespace at EOF.
    if (isBlank && this.leaf && this.leaf.t === 'table' &&
        (li < this.lines.length - 1 || this.endsWithNL)) {
      const rest = cursor.rest();
      let sp = 0;
      while (sp < rest.length && rest.charCodeAt(sp) === 32) sp++;
      if (sp <= 3 && sp + 1 === rest.length && rest.charCodeAt(sp) === 9) isBlank = false;
    }

    // An HTML block that ended on its first line keeps its trailing newline
    // unless the next line is empty after container-prefix removal (a
    // truly empty line, or a `>` quote-blank line). A whitespace-only line
    // (`\t`, ` `) does NOT clear it (marked keeps the `\n` there).
    if (this.htmlPending && this.htmlPending.nextLine === li) {
      if (cursor.i >= cursor.s.length && cursor.spaces === 0) this.htmlPending.node.keepNL = false;
      this.htmlPending = null;
    }

    // Phase 2: blank line.
    if (isBlank) {
      if (allMatched && this.leaf) {
        if (this.leaf.t === 'fence') {
          cursor.skipFenceIndent(this.leaf.fenceIndent);
          let rest = cursor.rest();
          if (this.stack.length > 1) rest = expandLeadingTabs(rest, cursor.col - this.tabBaseCol);
          this.leaf.lines.push(rest);
          return;
        }
        if (this.leaf.t === 'code') {
          // A blank line inside indented code keeps its content minus 4 cols.
          cursor.skipIndent(4);
          this.leaf.pendingBlankLines.push(cursor.rest());
          return;
        }
        if (this.leaf.t === 'html' && this.leaf.htmlType <= 5) {
          this.leaf.lines.push(cursor.rest());
          this.leaf.lastLineIdx = li;
          return;
        }
      }
      const deepest = this.stack[lastMatched];
      if (deepest.t === 'item') {
        // An empty list item is closed by a blank line.
        if (deepest.children.length === 0) lastMatched--;
      }
      // A blank line ends every open block: mark the rightmost path from
      // the GENUINE match depth so looseness can be decided when the next
      // block arrives. The genuine depth re-matches without the blank-line
      // free pass: an empty line is a top-level blank (marks from the doc,
      // so ancestors on the rightmost path are marked), while a line with
      // a '>' marker is genuinely inside the quote (marks only from there).
      let markDepth = 0;
      {
        const c2 = new LineCursor(line);
        for (let d = 1; d <= lastMatched; d++) {
          const container = this.stack[d];
          if (container.t === 'quote') {
            if (!this.matchBlockquote(c2)) break;
          } else if (container.t === 'item') {
            const need = container.contentIndent;
            if (need > 0 && c2.skipIndent(need) < need) break;
          }
          markDepth = d;
        }
      }
      let cur = this.stack[markDepth];
      while (cur) {
        cur.endsBlank = true;
        const ch = cur.children;
        if (!ch || ch.length === 0) break;
        cur = ch[ch.length - 1];
      }
      this.closeLeaf('blank');
      this.popTo(lastMatched + 1);
      return;
    }

    // Phase 3: lazy continuation or add to the open leaf.
    if (!allMatched) {
      // A fence or HTML block inside a list item swallows non-breaker
      // lines (marked: an unindented line inside a list-item fence is
      // fence content, not the end of the fence). Only when the first
      // unmatched container is an item (not a quote: quotes do not
      // swallow). Breakers (new blocks) still close the leaf.
      if (this.leaf && (this.leaf.t === 'fence' || this.leaf.t === 'html')) {
        let firstUnmatched = null;
        for (let d = lastMatched + 1; d < this.stack.length; d++) {
          const t = this.stack[d].t;
          if (t === 'quote' || t === 'item') { firstUnmatched = t; break; }
        }
        // The leaf must already have content to swallow: a fence needs a
        // content line (its opening line is not in lines), an HTML block
        // needs a line beyond its opening line. An HTML block that has
        // seen its closing tag no longer swallows.
        const leaf = this.leaf;
        const hasContent = leaf.t === 'fence' ? leaf.lines.length > 0 : leaf.lines.length > 1;
        if (firstUnmatched === 'item' && hasContent && !leaf.sawClose &&
            !this.startsInterruptBlock(cursor) &&
            !this.lineContinuesList(cursor, lastMatched) &&
            !this.startsListItemWithContent(cursor)) {
          if (this.addToLeaf(cursor)) return;
        }
      }
      if (this.leaf && this.leaf.t === 'para' && !this.startsInterruptBlock(cursor) &&
          !this.lineContinuesList(cursor, lastMatched) &&
          !this.startsListItemWithContent(cursor)) {
        let content = cursor.rest();
        const setextLike = isSetextLine(content);
        // Marked quirk: a lazy setext-like line in a blockquote, following
        // another lazy line, is re-indented to 4 spaces (so it stays text).
        const parent = this.stack[this.stack.length - 1];
        if (parent.t === 'quote' && this.leaf.lastLazy && setextLike) {
          let sp = 0;
          while (sp < content.length && content.charCodeAt(sp) === 32) sp++;
          if (sp <= 3 && sp < content.length) {
            const c0 = content.charCodeAt(sp);
            if (c0 === 61 || c0 === 45) content = '    ' + content.slice(sp);
          }
        } else if (!setextLike && cursor.indentAvailable() >= 4) {
          // A lazy line with 4+ columns of indent loses 4 (as if for code).
          cursor.skipIndent(4);
          content = cursor.rest();
        }
        if (this.stack.length > 1) content = expandLeadingTabs(content, cursor.col - this.tabBaseCol);
        this.leaf.lines.push(content);
        this.leaf.lastLazy = true;
        return;
      }
      this.closeLeaf('other');
      this.popTo(lastMatched + 1);
    } else if (this.leaf) {
      if (this.addToLeaf(cursor)) return;
    }

    // Phase 4: start new blocks.
    this.openNewBlocks(cursor);
  }

  matchBlockquote(cursor) {
    const saved = cursor.save();
    cursor.skipIndent(3);
    if (cursor.cur() !== 62) { cursor.restore(saved); return false; }
    cursor.advance();
    // Only a literal space is consumed after `>`; a tab stays as content
    // so its expansion uses the effective (tabBaseCol-adjusted) column
    // (marked: `>\t` in a nested quote expands to 2 spaces, not 3).
    if (cursor.cur() === 32) cursor.consumeOneColumn();
    return true;
  }

  matchListItem(cursor, item) {
    if (cursor.isBlank()) return true;
    const saved = cursor.save();
    // contentIndent is relative to the parent container's content start,
    // which is where the cursor sits after the parents matched.
    // A blank line matches only with enough indent: an empty line is a
    // top-level blank line, not one inside the item.
    const need = item.contentIndent;
    if (need > 0) {
      const skipped = cursor.skipIndent(need);
      if (skipped < need) { cursor.restore(saved); return false; }
    }
    return true;
  }

  stripParagraphDefs(leaf) {
    const content = leaf.lines.join('\n');
    let pos = 0;
    while (true) {
      const def = parseLinkRefDef(content, pos);
      if (!def) break;
      const norm = normalizeLabel(def.label);
      if (norm !== '' && !this.refs.has(norm)) {
        this.refs.set(norm, { href: def.href, title: def.title });
      }
      pos = def.endPos;
    }
    const rest = content.slice(pos);
    leaf.lines = rest === '' ? [] : rest.split('\n');
    return rest;
  }

  closeLeaf(reason) {
    if (!this.leaf) return;
    const leaf = this.leaf;
    this.leaf = null;
    if (reason === 'blank') leaf.endsBlank = true;
    if (leaf.t === 'para') {
      const rest = this.stripParagraphDefs(leaf);
      if (rest === '') {
        const parent = this.stack[this.stack.length - 1];
        if (parent.children[parent.children.length - 1] === leaf) parent.children.pop();
      } else {
        leaf.content = rest;
        leaf.lines = null;
      }
    } else if (leaf.t === 'html') {
      leaf.lastTerm = leaf.lastLineIdx < this.lines.length - 1 || this.endsWithNL;
      if (leaf.htmlType <= 5) {
        leaf.keepNL = reason === 'eof' ? true : this.lines[this.curLine] !== '';
      } else {
        // Types 6-7: the trailing newline is kept only when the block runs
        // to the end of the input.
        leaf.keepNL = reason === 'eof';
      }
    } else if (leaf.t === 'fence') {
      if (leaf.lines.length > 0 && leaf.lines[leaf.lines.length - 1] === '') leaf.lines.pop();
    }
  }

  addBlock(block) {
    // A list can only contain items; close a dangling list on the stack top.
    while (this.stack[this.stack.length - 1].t === 'list') {
      const node = this.stack.pop();
      this.trimListTail(node);
    }
    const parent = this.stack[this.stack.length - 1];
    if (parent.t === 'item' && parent.children.length > 0) {
      // A new block in an item after a blank line makes the list loose.
      const prev = parent.children[parent.children.length - 1];
      if (prev.endsBlank) {
        const list = this.stack[this.stack.length - 2];
        if (list && list.t === 'list') list.tight = false;
      }
    }
    parent.children.push(block);
    this.clearEndsBlank();
  }

  // A new block anywhere inside a container means it no longer ends blank.
  clearEndsBlank() {
    for (let d = 0; d < this.stack.length; d++) this.stack[d].endsBlank = false;
  }

  // --- leaf continuation ---

  addToLeaf(cursor) {
    const leaf = this.leaf;
    if (leaf.t === 'para') return this.addToParagraph(cursor);
    if (leaf.t === 'fence') {
      const saved = cursor.save();
      cursor.skipIndent(3);
      const c = cursor.cur();
      if (c === leaf.fenceCharCode) {
        let j = cursor.i;
        let count = 0;
        while (j < cursor.s.length && cursor.s.charCodeAt(j) === c) { count++; j++; }
        if (count >= leaf.fenceLen) {
          let k = j;
          let onlyWs = true;
          while (k < cursor.s.length) {
            const cc = cursor.s.charCodeAt(k);
            if (cc !== 32 && cc !== 9) { onlyWs = false; break; }
            k++;
          }
          if (onlyWs) {
            leaf.closed = true;
            // A fenced code block drops one trailing empty line.
            if (leaf.lines.length > 0 && leaf.lines[leaf.lines.length - 1] === '') leaf.lines.pop();
            this.leaf = null;
            return true;
          }
        }
      }
      cursor.restore(saved);
      cursor.skipFenceIndent(leaf.fenceIndent);
      let fenceRest = cursor.rest();
      if (this.stack.length > 1) fenceRest = expandLeadingTabs(fenceRest, cursor.col - this.tabBaseCol);
      leaf.lines.push(fenceRest);
      return true;
    }
    if (leaf.t === 'code') {
      if (cursor.indentAvailable() >= 4) {
        cursor.skipIndent(4);
        for (const bl of leaf.pendingBlankLines) leaf.lines.push(bl);
        leaf.pendingBlankLines.length = 0;
        leaf.lines.push(cursor.rest());
        return true;
      }
      this.leaf = null;
      return false;
    }
    if (leaf.t === 'html') {
      const rest = cursor.rest();
      leaf.lines.push(rest);
      leaf.lastLineIdx = this.curLine;
      if (leaf.htmlClose && rest.trimStart().toLowerCase().startsWith(leaf.htmlClose)) leaf.sawClose = true;
      if (leaf.htmlType <= 5) {
        let found;
        if (leaf.htmlType === 1) found = rest.toLowerCase().indexOf(leaf.htmlEnd) !== -1;
        else found = rest.indexOf(leaf.htmlEnd) !== -1;
        if (found) {
          leaf.keepNL = true;
          leaf.lastTerm = this.curLine < this.lines.length - 1 || this.endsWithNL;
          this.htmlPending = { node: leaf, nextLine: this.curLine + 1 };
          this.leaf = null;
        }
      }
      return true;
    }
    if (leaf.t === 'table') {
      // A line of 0-3 spaces + exactly one tab is an empty row.
      const rest0 = cursor.rest();
      let sp0 = 0;
      while (sp0 < rest0.length && rest0.charCodeAt(sp0) === 32) sp0++;
      if (sp0 <= 3 && sp0 + 1 === rest0.length && rest0.charCodeAt(sp0) === 9) {
        leaf.rows.push(new Array(leaf.header.length).fill(''));
        return true;
      }
      if (cursor.indentAvailable() >= 4 || this.startsInterruptBlock(cursor)) {
        this.leaf = null;
        return false;
      }
      cursor.skipIndent(3);
      const cells = splitTableRow(cursor.rest());
      while (cells.length < leaf.header.length) cells.push('');
      if (cells.length > leaf.header.length) cells.length = leaf.header.length;
      leaf.rows.push(cells);
      return true;
    }
    return false;
  }

  addToParagraph(cursor) {
    const leaf = this.leaf;
    let newLine = cursor.rest();
    // Inside a container, leading tabs of a paragraph line expand to
    // spaces (top-level lines keep their tabs verbatim).
    if (this.stack.length > 1) newLine = expandLeadingTabs(newLine, cursor.col - this.tabBaseCol);
    // If the new line continues a pending link ref def (a dest or title
    // line), absorb it: finalizing the def now would lose the title.
    const content = leaf.lines.join('\n');
    if (defsEndPos(content + '\n' + newLine) > content.length + 1) {
      leaf.lines.push(newLine);
      leaf.lastLazy = false;
      return true;
    }
    const rest = this.stripParagraphDefs(leaf);
    if (rest !== '') {
      const saved = cursor.save();
      if (cursor.indentAvailable() < 4) {
        cursor.skipIndent(3);
        const setext = this.parseSetext(cursor);
        if (setext !== 0) {
          const parent = this.stack[this.stack.length - 1];
          parent.children.pop();
          parent.children.push({ t: 'heading', level: setext, content: trimWs(rest) });
          this.leaf = null;
          return true;
        }
      }
      cursor.restore(saved);
      const delim = this.parseTableDelimiter(cursor, leaf);
      if (delim) {
        const parent = this.stack[this.stack.length - 1];
        const headerLine = leaf.lines.pop();
        const headerCells = splitTableRow(headerLine);
        if (leaf.lines.length === 0) {
          parent.children.pop();
        } else {
          leaf.content = leaf.lines.join('\n');
          leaf.lines = null;
        }
        const table = { t: 'table', align: delim, header: headerCells, rows: [] };
        parent.children.push(table);
        this.leaf = table;
        return true;
      }
      cursor.restore(saved);
    }
    if (this.startsInterruptBlock(cursor)) {
      this.closeLeaf('other');
      return false;
    }
    leaf.lines.push(newLine);
    leaf.lastLazy = false;
    return true;
  }

  parseSetext(cursor) {
    const c = cursor.cur();
    if (c !== 61 && c !== 45) return 0;
    let j = cursor.i;
    const s = cursor.s;
    let count = 0;
    while (j < s.length && s.charCodeAt(j) === c) { count++; j++; }
    if (count === 0) return 0;
    while (j < s.length) {
      const cc = s.charCodeAt(j);
      if (cc === 32 || cc === 9) j++;
      else return 0;
    }
    return c === 61 ? 1 : 2;
  }

  parseTableDelimiter(cursor, leaf) {
    if (leaf.lines.length === 0) return null;
    if (cursor.indentAvailable() >= 4) return null;
    const saved = cursor.save();
    cursor.skipIndent(3);
    const rest = cursor.rest();
    cursor.restore(saved);
    const align = parseDelimiterRow(rest);
    if (!align) return null;
    const headerCells = splitTableRow(leaf.lines[leaf.lines.length - 1]);
    if (headerCells.length !== align.length) return null;
    return align;
  }

  // --- block-start recognition ---

  isAtx(cursor) {
    let count = 0;
    let j = cursor.i;
    const s = cursor.s;
    while (j < s.length && s.charCodeAt(j) === 35) { count++; j++; }
    if (count < 1 || count > 6) return false;
    if (j >= s.length) return true;
    const after = s.charCodeAt(j);
    return after === 32 || after === 9;
  }

  isFence(cursor) {
    const c = cursor.cur();
    let count = 0;
    let j = cursor.i;
    const s = cursor.s;
    while (j < s.length && s.charCodeAt(j) === c) { count++; j++; }
    if (count < 3) return false;
    if (c === 96 && s.indexOf('`', j) !== -1) return false;
    return true;
  }

  isHr(cursor) {
    const c = cursor.cur();
    if (c !== 42 && c !== 45 && c !== 95) return false;
    let count = 0;
    let j = cursor.i;
    const s = cursor.s;
    while (j < s.length) {
      const cc = s.charCodeAt(j);
      if (cc === c) { count++; j++; }
      else if (cc === 32 || cc === 9) j++;
      else return false;
    }
    return count >= 3;
  }

  isBulletList(cursor) {
    const c = cursor.cur();
    if (c !== 45 && c !== 43 && c !== 42) return false;
    const next = cursor.i + 1 >= cursor.s.length ? -1 : cursor.s.charCodeAt(cursor.i + 1);
    return next === -1 || next === 32 || next === 9;
  }

  isOrderedList(cursor) {
    let j = cursor.i;
    const s = cursor.s;
    let num = 0;
    let digits = 0;
    while (j < s.length && digits < 10) {
      const cc = s.charCodeAt(j);
      if (cc >= 48 && cc <= 57) { num = num * 10 + (cc - 48); digits++; j++; }
      else break;
    }
    if (digits === 0 || digits > 9) return null;
    if (j >= s.length) return null;
    const delim = s.charCodeAt(j);
    if (delim !== 46 && delim !== 41) return null;
    j++;
    const after = j >= s.length ? -1 : s.charCodeAt(j);
    if (after !== -1 && after !== 32 && after !== 9) return null;
    return { num, delim: delim === 46 ? '.' : ')', width: j - cursor.i };
  }

  startsInterruptBlock(cursor) {
    const saved = cursor.save();
    if (cursor.indentAvailable() >= 4) { cursor.restore(saved); return false; }
    cursor.skipIndent(3);
    const c = cursor.cur();
    let result = false;
    if (c === 35) result = this.isAtx(cursor);
    else if (c === 96 || c === 126) result = this.isFence(cursor);
    else if (c === 60) {
      const hb = htmlBlockType(cursor.rest());
      result = !!(hb && hb.type <= 6);
    } else if (c === 62) result = true;
    else if (c === 42 || c === 45 || c === 95) {
      // An empty list item cannot interrupt a paragraph.
      result = this.isHr(cursor) || (this.isBulletList(cursor) && this.listHasContent(cursor, 1));
    } else if (c === 43) result = this.isBulletList(cursor) && this.listHasContent(cursor, 1);
    else if (c >= 48 && c <= 57) {
      const ol = this.isOrderedList(cursor);
      // An ordered list can interrupt a paragraph if it starts with 1, or
      // if the paragraph's parent is a list item (any start number then
      // works: the list is a new block in the item, not a lazy line).
      const parentIsItem = this.stack.length > 0 && this.stack[this.stack.length - 1].t === 'item';
      result = !!(ol && (ol.num === 1 || parentIsItem) && this.listHasContent(cursor, ol.width));
    }
    cursor.restore(saved);
    return result;
  }

  // Does this line start a new item of the list at stack[lastMatched]?
  // (Ordered lists starting with 2+ do not interrupt a paragraph, but they
  // still start a new item of an open list instead of lazily continuing it.)
  lineContinuesList(cursor, lastMatched) {
    const container = this.stack[lastMatched];
    if (!container || container.t !== 'list') return false;
    const saved = cursor.save();
    if (cursor.indentAvailable() >= 4) { cursor.restore(saved); return false; }
    cursor.skipIndent(3);
    const info = this.parseListMarker(cursor);
    cursor.restore(saved);
    if (!info) return false;
    const sameType = container.ordered === info.ordered;
    const sameDelim = !info.ordered ? container.marker === info.marker : container.delim === info.delim;
    return sameType && sameDelim;
  }

  // Is there non-whitespace content after a list marker of the given width?
  listHasContent(cursor, width) {
    let j = cursor.i + width;
    const s = cursor.s;
    while (j < s.length) {
      const c = s.charCodeAt(j);
      if (c === 32 || c === 9) j++;
      else return true;
    }
    return false;
  }

  // Does this line start a list item (any list) with content on the line?
  startsListItemWithContent(cursor) {
    const saved = cursor.save();
    if (cursor.indentAvailable() >= 4) { cursor.restore(saved); return false; }
    cursor.skipIndent(3);
    const info = this.parseListMarker(cursor);
    if (!info) { cursor.restore(saved); return false; }
    const hasContent = this.listHasContent(cursor, info.width);
    cursor.restore(saved);
    return hasContent;
  }

  parseListMarker(cursor) {
    const c = cursor.cur();
    const s = cursor.s;
    if (c === 45 || c === 43 || c === 42) {
      const next = cursor.i + 1 >= s.length ? -1 : s.charCodeAt(cursor.i + 1);
      if (next !== -1 && next !== 32 && next !== 9) return null;
      return { ordered: false, marker: c === 45 ? '-' : c === 43 ? '+' : '*', num: 0, delim: null, width: 1, markerCol: cursor.col };
    }
    if (c >= 48 && c <= 57) {
      const ol = this.isOrderedList(cursor);
      if (!ol) return null;
      return { ordered: true, marker: null, num: ol.num, delim: ol.delim, width: ol.width, markerCol: cursor.col };
    }
    return null;
  }

  openListItem(cursor, info, parentCol) {
    const markerEndCol = info.markerCol + info.width;
    for (let k = 0; k < info.width; k++) cursor.advance();
    const ws = cursor.measureWhitespace();
    let contentIndent;
    if (ws.blank) {
      contentIndent = markerEndCol + 1;
      cursor.skipIndent(ws.columns);
    } else if (ws.columns >= 1 && ws.columns <= 4) {
      contentIndent = ws.endCol;
      cursor.skipIndent(ws.columns);
    } else {
      contentIndent = markerEndCol + 1;
      cursor.skipIndent(1);
    }
    // Store the indent relative to the parent container's content start:
    // the parent's prefix width varies by line (e.g. '> > ' vs '>>').
    contentIndent -= parentCol;
    const parent = this.stack[this.stack.length - 1];
    let list = null;
    if (parent.t === 'list') {
      const sameType = parent.ordered === info.ordered;
      const sameDelim = !info.ordered ? parent.marker === info.marker : parent.delim === info.delim;
      if (sameType && sameDelim) list = parent;
      else this.stack.pop();
    }
    if (!list) {
      list = { t: 'list', ordered: info.ordered, marker: info.marker, delim: info.delim, start: info.num, tight: true, children: [] };
      this.addBlock(list);
      this.stack.push(list);
    } else if (list.children.length > 0) {
      // A new item after a blank line makes the list loose.
      const prev = list.children[list.children.length - 1];
      if (prev.endsBlank) list.tight = false;
    }
    this.clearEndsBlank();
    const item = { t: 'item', contentIndent, children: [] };
    list.children.push(item);
    this.stack.push(item);
  }

  // --- phase 4: start new blocks ---

  openNewBlocks(cursor) {
    while (true) {
      const colBefore = cursor.col;
      if (cursor.indentAvailable() >= 4) {
        cursor.skipIndent(4);
        const code = { t: 'code', lines: [cursor.rest()], pendingBlankLines: [] };
        this.addBlock(code);
        this.leaf = code;
        return;
      }
      // Save the pre-indent position: a paragraph keeps its leading spaces.
      const pi = cursor.i, pc = cursor.col, ps = cursor.spaces;
      const indentSkipped = cursor.skipIndent(3);
      const c = cursor.cur();
      if (c === 62) { // blockquote
        cursor.advance();
        if (cursor.cur() === 32 || cursor.cur() === 9) cursor.consumeOneColumn();
        const quote = { t: 'quote', children: [] };
        this.addBlock(quote);
        this.stack.push(quote);
        if (cursor.isBlank()) return;
        continue;
      }
      if ((c === 42 || c === 45 || c === 95) && this.isHr(cursor)) {
        this.addBlock({ t: 'hr' });
        return;
      }
      const listInfo = this.parseListMarker(cursor);
      if (listInfo) {
        this.openListItem(cursor, listInfo, pc);
        if (cursor.isBlank()) return;
        continue;
      }
      if (c === 35 && this.isAtx(cursor)) {
        let j = cursor.i;
        let level = 0;
        while (j < cursor.s.length && cursor.s.charCodeAt(j) === 35) { level++; j++; }
        let content = cursor.s.slice(j);
        content = content.replace(/[ \t]+$/, '');
        const m = content.match(/[ \t]+#+$/);
        if (m) content = content.slice(0, content.length - m[0].length);
        content = content.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
        this.addBlock({ t: 'heading', level, content });
        return;
      }
      if ((c === 96 || c === 126) && this.isFence(cursor)) {
        const fenceCharCode = c;
        let j = cursor.i;
        let len = 0;
        while (j < cursor.s.length && cursor.s.charCodeAt(j) === c) { len++; j++; }
        const info = cursor.s.slice(j).trim();
        const sp = info.search(/[ \t]/);
        const lang = unescapeInline(sp === -1 ? info : info.slice(0, sp));
        // Marked strips the opening fence's indent from content lines
        // for backtick fences only; tilde-fence content keeps its full
        // indent (marked: `   ~~~\n   x\n   ~~~` -> `   x`).
        const fence = { t: 'fence', fenceCharCode, fenceLen: len, fenceIndent: c === 96 ? indentSkipped : 0, lang, lines: [], closed: false };
        this.addBlock(fence);
        this.leaf = fence;
        return;
      }
      if (c === 60) {
        const hb = htmlBlockType(cursor.rest());
        if (hb) {
          // The HTML block's first line keeps its leading spaces.
          cursor.i = pi; cursor.col = pc; cursor.spaces = ps;
          const line = cursor.rest();
          const html = { t: 'html', htmlType: hb.type, htmlEnd: hb.end, lines: [line], keepNL: true, lastTerm: true, lastLineIdx: this.curLine };
          this.addBlock(html);
          this.leaf = html;
          // For type 6, remember the closing tag: once a line contains
          // it, the block no longer swallows unindented lines in a list.
          if (hb.type === 6) {
            const t = line.trimStart();
            if (t.charCodeAt(0) === 60 && t.length > 1 && isAsciiLetter(t.charCodeAt(1))) {
              let k = 1;
              while (k < t.length) {
                const cc = t.charCodeAt(k);
                if (!isAsciiLetter(cc) && !isDigitCode(cc) && cc !== 45) break;
                k++;
              }
              html.htmlClose = '</' + t.slice(1, k).toLowerCase() + '>';
              if (line.toLowerCase().indexOf(html.htmlClose) !== -1) html.sawClose = true;
            }
          }
          if (hb.type <= 5) {
            let found;
            if (hb.type === 1) found = line.toLowerCase().indexOf(hb.end) !== -1;
            else found = line.indexOf(hb.end) !== -1;
            if (found) {
              html.keepNL = true;
              html.lastTerm = this.curLine < this.lines.length - 1 || this.endsWithNL;
              this.htmlPending = { node: html, nextLine: this.curLine + 1 };
              this.leaf = null;
            }
          }
          return;
        }
      }
      // Paragraph (link ref defs are stripped when it closes).
      // Restore the pre-indent cursor: paragraph content keeps leading spaces.
      cursor.i = pi; cursor.col = pc; cursor.spaces = ps;
      // A whitespace-only line does not start a paragraph.
      if (cursor.isBlank()) return;
      let firstLine = cursor.rest();
      if (this.stack.length > 1) firstLine = expandLeadingTabs(firstLine, pc - this.tabBaseCol);
      const para = { t: 'para', lines: [firstLine], task: null, content: null, lastLazy: false };
      const parent = this.stack[this.stack.length - 1];
      if (parent.t === 'item' && parent.children.length === 0) {
        const line = para.lines[0];
        let ms = 0;
        while (ms < line.length && (line.charCodeAt(ms) === 32 || line.charCodeAt(ms) === 9)) ms++;
        if (line.length - ms >= 4 && line.charCodeAt(ms) === 91 && line.charCodeAt(ms + 2) === 93) {
          const m = line.charCodeAt(ms + 1);
          const after = line.charCodeAt(ms + 3);
          if ((m === 32 || m === 120 || m === 88) && (after === 32 || after === 9)) {
            para.task = m === 32 ? 'unchecked' : 'checked';
            para.lines[0] = line.slice(ms + 3);
          }
        }
      }
      this.addBlock(para);
      this.leaf = para;
      return;
    }
  }
}

// ---------------------------------------------------------------------------
// Block rendering
// ---------------------------------------------------------------------------

function renderBlocks(blocks, refs) {
  let out = '';
  for (const b of blocks) out += renderBlock(b, refs);
  return out;
}

function renderBlock(b, refs) {
  switch (b.t) {
    case 'quote':
      return '<blockquote>\n' + renderBlocks(b.children, refs) + '</blockquote>\n';
    case 'list': {
      const tag = b.ordered ? 'ol' : 'ul';
      const start = b.ordered && b.start !== 1 ? ' start="' + b.start + '"' : '';
      let out = '<' + tag + start + '>\n';
      for (const item of b.children) out += renderItem(item, b.tight, refs);
      return out + '</' + tag + '>\n';
    }
    case 'para': {
      let inner = '';
      if (b.task) inner += b.task === 'checked' ? '<input checked="" disabled="" type="checkbox">' : '<input disabled="" type="checkbox">';
      inner += parseInline(b.content, refs);
      return '<p>' + inner + '</p>\n';
    }
    case 'heading':
      return '<h' + b.level + '>' + parseInline(b.content, refs) + '</h' + b.level + '>\n';
    case 'code':
      return '<pre><code>' + escapeUncond(b.lines.join('\n') + '\n') + '</code></pre>\n';
    case 'fence': {
      const lang = b.lang ? ' class="language-' + escapeHref(b.lang) + '"' : '';
      const body = b.lines.length ? b.lines.join('\n') + '\n' : '';
      return '<pre><code' + lang + '>' + escapeUncond(body) + '</code></pre>\n';
    }
    case 'html': {
      const text = b.lines.join('\n') + (b.keepNL && b.lastTerm ? '\n' : '');
      return text;
    }
    case 'hr':
      return '<hr>\n';
    case 'table': {
      let out = '<table>\n<thead>\n<tr>\n';
      for (let i = 0; i < b.header.length; i++) {
        const align = b.align[i];
        out += '<th' + (align ? ' align="' + align + '"' : '') + '>' + parseInline(b.header[i], refs) + '</th>\n';
      }
      out += '</tr>\n</thead>\n';
      if (b.rows.length > 0) {
        out += '<tbody>';
        for (const row of b.rows) {
          out += '<tr>\n';
          for (let i = 0; i < row.length; i++) {
            const align = b.align[i];
            out += '<td' + (align ? ' align="' + align + '"' : '') + '>' + parseInline(row[i], refs) + '</td>\n';
          }
          out += '</tr>\n';
        }
        out += '</tbody>';
      }
      out += '</table>\n';
      return out;
    }
  }
  return '';
}

function renderItem(item, tight, refs) {
  let out = '<li>';
  if (tight) {
    for (const child of item.children) {
      if (child.t === 'para') {
        if (child.task) out += child.task === 'checked' ? '<input checked="" disabled="" type="checkbox">' : '<input disabled="" type="checkbox">';
        out += parseInline(child.content, refs);
      } else {
        out += renderBlock(child, refs);
      }
    }
    out += '</li>\n';
  } else {
    for (const child of item.children) out += renderBlock(child, refs);
    out += '</li>\n';
  }
  return out;
}
