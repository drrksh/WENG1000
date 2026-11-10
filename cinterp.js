/* cinterp.js - a teaching C interpreter with dcc-style runtime checks.
 * Supports the C used in a first programming course: int/char/double/long,
 * pointers, 1D/2D arrays, structs, typedef, enum, malloc/free, strings,
 * stdio/stdlib/string/ctype/math/assert. Detects NULL dereference, array
 * index out of bounds, uninitialized reads, use after free, double free,
 * writes to string literals and memory leaks.
 * API: CInterp.run(source, input, {stepLimit}) -> result object.
 */
(function (root) {
  'use strict';

  // ------------------------------------------------------------------ errors
  function CError(kind, msg, line, col) {
    this.kind = kind; this.msg = msg; this.line = line || 0; this.col = col || 0;
  }
  function ExitSignal(code) { this.code = code; }
  function cerr(msg, node) { throw new CError('compile', msg, node && node.line, node && node.col); }

  // ------------------------------------------------------------------ lexer
  var KEYWORDS = {};
  ('int char short long float double void unsigned signed struct union enum typedef const volatile ' +
    'static extern register inline if else while do for return break continue switch case default ' +
    'sizeof goto _Bool bool auto restrict').split(' ').forEach(function (k) { KEYWORDS[k] = true; });
  var PUNCT = ['...', '<<=', '>>=', '->', '++', '--', '<<', '>>', '<=', '>=', '==', '!=', '&&', '||',
    '+=', '-=', '*=', '/=', '%=', '&=', '^=', '|=', '+', '-', '*', '/', '%', '=', '<', '>', '!', '~', '&',
    '|', '^', '?', ':', ';', ',', '.', '(', ')', '[', ']', '{', '}', '#'];

  function utf8(str) {
    var out = [];
    for (var i = 0; i < str.length; i++) {
      var c = str.codePointAt(i);
      if (c > 0xffff) i++;
      if (c < 0x80) out.push(c);
      else if (c < 0x800) out.push(0xc0 | (c >> 6), 0x80 | (c & 63));
      else if (c < 0x10000) out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63));
      else out.push(0xf0 | (c >> 18), 0x80 | ((c >> 12) & 63), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63));
    }
    return out;
  }

  function lex(src) {
    var toks = [];
    var i = 0, line = 1, lineStart = 0, n = src.length;
    var atLineStart = true;
    function err(msg) { throw new CError('compile', msg, line, i - lineStart + 1); }
    function readEscape() {
      // src[i] is the char after backslash
      var c = src[i++];
      switch (c) {
        case 'n': return 10; case 't': return 9; case 'r': return 13; case '0':
          if (/[0-7]/.test(src[i] || '')) { var o = '0'; while (/[0-7]/.test(src[i] || '') && o.length < 3) o += src[i++]; return parseInt(o, 8) & 255; }
          return 0;
        case '\\': return 92; case '\'': return 39; case '"': return 34; case '?': return 63;
        case 'a': return 7; case 'b': return 8; case 'f': return 12; case 'v': return 11; case 'e': return 27;
        case 'x': var h = ''; while (/[0-9a-fA-F]/.test(src[i] || '')) h += src[i++]; if (!h) err('\\x used with no following hex digits'); return parseInt(h, 16) & 255;
        default:
          if (/[1-7]/.test(c)) { var oc = c; while (/[0-7]/.test(src[i] || '') && oc.length < 3) oc += src[i++]; return parseInt(oc, 8) & 255; }
          if (c === undefined || c === '\n') err('missing terminating character');
          return c.charCodeAt(0);
      }
    }
    while (i < n) {
      var c = src[i];
      if (c === '\n') { i++; line++; lineStart = i; atLineStart = true; continue; }
      if (c === ' ' || c === '\t' || c === '\r' || c === '\f' || c === '\v') { i++; continue; }
      if (c === '\\' && src[i + 1] === '\n') { i += 2; line++; lineStart = i; continue; }
      if (c === '/' && src[i + 1] === '/') { while (i < n && src[i] !== '\n') i++; continue; }
      if (c === '/' && src[i + 1] === '*') {
        var end = src.indexOf('*/', i + 2);
        if (end < 0) err('unterminated /* comment');
        for (var k = i; k < end; k++) if (src[k] === '\n') { line++; lineStart = k + 1; }
        i = end + 2; continue;
      }
      var startCol = i - lineStart + 1, s = i;
      if (c === '#' && atLineStart) {
        // preprocessor directive: read the whole logical line
        var j = i + 1, text = '';
        while (j < n && src[j] !== '\n') {
          if (src[j] === '\\' && src[j + 1] === '\n') { j += 2; line++; text += ' '; continue; }
          text += src[j]; j++;
        }
        // strip comments in directive
        text = text.replace(/\/\*[\s\S]*?\*\//g, ' ').replace(/\/\/.*$/, '');
        toks.push({ t: 'pp', v: text.trim(), line: line, col: startCol, s: s, e: j });
        i = j; continue;
      }
      atLineStart = false;
      if (/[A-Za-z_]/.test(c)) {
        var j2 = i; while (j2 < n && /[A-Za-z0-9_]/.test(src[j2])) j2++;
        var word = src.slice(i, j2);
        toks.push({ t: KEYWORDS[word] ? 'kw' : 'id', v: word, line: line, col: startCol, s: s, e: j2 });
        i = j2; continue;
      }
      if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(src[i + 1] || ''))) {
        var m = /^(0[xX][0-9a-fA-F]+|(?:[0-9]+\.?[0-9]*|\.[0-9]+)(?:[eE][+-]?[0-9]+)?)([uUlLfF]*)/.exec(src.slice(i, i + 64));
        var body = m[1], suf = m[2].toLowerCase();
        var isFloat = !/^0[xX]/.test(body) && /[.eE]/.test(body);
        if (suf.indexOf('f') >= 0 && !isFloat && !/^0[xX]/.test(body)) err('invalid suffix on integer constant');
        var val;
        if (isFloat) val = parseFloat(body);
        else if (/^0[xX]/.test(body)) val = parseInt(body, 16);
        else if (body.length > 1 && body[0] === '0') { if (/[89]/.test(body)) err('invalid digit in octal constant'); val = parseInt(body, 8); }
        else val = parseInt(body, 10);
        var after = src[i + m[0].length] || '';
        if (/[A-Za-z_0-9]/.test(after)) err('invalid suffix on number');
        toks.push({ t: 'num', v: val, isFloat: isFloat, isLong: suf.indexOf('l') >= 0, isUnsigned: suf.indexOf('u') >= 0, line: line, col: startCol, s: s, e: i + m[0].length });
        i += m[0].length; continue;
      }
      if (c === '\'') {
        i++;
        if (src[i] === '\'') err('empty character constant');
        var cv;
        if (src[i] === '\\') { i++; cv = readEscape(); }
        else { var bytes = utf8(String.fromCodePoint(src.codePointAt(i))); i += (src.codePointAt(i) > 0xffff ? 2 : 1); cv = bytes.length === 1 ? bytes[0] : bytes[bytes.length - 1]; }
        if (src[i] !== '\'') err('missing terminating \' character (character constants hold ONE character; use "double quotes" for strings)');
        i++;
        if (cv > 127) cv -= 256;
        toks.push({ t: 'num', v: cv, isChar: true, line: line, col: startCol, s: s, e: i });
        continue;
      }
      if (c === '"') {
        i++; var bytesS = [];
        while (true) {
          if (i >= n || src[i] === '\n') err('missing terminating " character');
          if (src[i] === '"') { i++; break; }
          if (src[i] === '\\') { i++; bytesS.push(readEscape()); continue; }
          var cp = src.codePointAt(i); i += cp > 0xffff ? 2 : 1;
          Array.prototype.push.apply(bytesS, utf8(String.fromCodePoint(cp)));
        }
        toks.push({ t: 'str', v: bytesS, line: line, col: startCol, s: s, e: i });
        continue;
      }
      var p = null;
      for (var q = 0; q < PUNCT.length; q++) { if (src.startsWith(PUNCT[q], i)) { p = PUNCT[q]; break; } }
      if (!p) err('unexpected character \'' + c + '\'');
      toks.push({ t: 'op', v: p, line: line, col: startCol, s: s, e: i + p.length });
      i += p.length;
    }
    toks.push({ t: 'eof', v: '', line: line, col: i - lineStart + 1, s: n, e: n });
    return toks;
  }

  // ------------------------------------------------------------------ preprocessor
  var HEADER_OK = { 'stdio.h': 1, 'stdlib.h': 1, 'string.h': 1, 'ctype.h': 1, 'math.h': 1, 'assert.h': 1, 'stdbool.h': 1, 'limits.h': 1, 'time.h': 1, 'stddef.h': 1, 'stdint.h': 1, 'float.h': 1, 'unistd.h': 1, 'errno.h': 1 };

  function preprocess(toks) {
    var includes = {};
    var macros = {};
    function defineText(name, text) { macros[name] = { params: null, body: lex(text).slice(0, -1) }; }
    defineText('NULL', '((void *) 0)');
    defineText('EOF', '(-1)');
    defineText('true', '1'); defineText('false', '0');
    defineText('INT_MAX', '2147483647'); defineText('INT_MIN', '(-2147483647 - 1)');
    defineText('UINT_MAX', '4294967295U');
    defineText('CHAR_MAX', '127'); defineText('CHAR_MIN', '(-128)');
    defineText('LONG_MAX', '9007199254740991L'); defineText('LONG_MIN', '(-9007199254740991L)');
    defineText('RAND_MAX', '2147483647');
    defineText('EXIT_SUCCESS', '0'); defineText('EXIT_FAILURE', '1');
    defineText('BUFSIZ', '8192');
    defineText('M_PI', '3.14159265358979323846');
    var out = [];
    var input = toks.slice();
    var skipping = [];   // stack of booleans for #if / #ifdef
    function active() { for (var k = 0; k < skipping.length; k++) if (skipping[k]) return false; return true; }
    var idx = 0;
    while (idx < input.length) {
      var tk = input[idx];
      if (tk.t === 'pp') {
        idx++;
        var m = /^(\w+)\s*([\s\S]*)$/.exec(tk.v);
        if (!m) continue;
        var dir = m[1], rest = m[2];
        if (dir === 'ifdef' || dir === 'ifndef') {
          var nm = rest.trim().split(/\s+/)[0];
          var def = Object.prototype.hasOwnProperty.call(macros, nm);
          skipping.push(dir === 'ifdef' ? !def : def); continue;
        }
        if (dir === 'if') { skipping.push(/^\s*0\s*$/.test(rest)); continue; }
        if (dir === 'else') { if (skipping.length) skipping[skipping.length - 1] = !skipping[skipping.length - 1]; continue; }
        if (dir === 'elif') { if (skipping.length) skipping[skipping.length - 1] = true; continue; }
        if (dir === 'endif') { skipping.pop(); continue; }
        if (!active()) continue;
        if (dir === 'include') {
          var hm = /^[<"]([^>"]+)[>"]/.exec(rest.trim());
          if (!hm) throw new CError('compile', '#include expects <file.h>', tk.line, tk.col);
          if (!HEADER_OK[hm[1]]) throw new CError('compile', "'" + hm[1] + "' file not found (only standard headers are available here)", tk.line, tk.col);
          includes[hm[1]] = true;
        } else if (dir === 'define') {
          var dm = /^([A-Za-z_]\w*)(\([^)]*\))?\s*([\s\S]*)$/.exec(rest);
          if (!dm) throw new CError('compile', 'macro name missing in #define', tk.line, tk.col);
          var params = null;
          if (dm[2]) params = dm[2].slice(1, -1).split(',').map(function (x) { return x.trim(); }).filter(function (x) { return x; });
          var bodyToks;
          try { bodyToks = lex(dm[3]).slice(0, -1); } catch (e) { throw new CError('compile', e.msg || 'bad #define', tk.line, tk.col); }
          if (/=/.test(dm[3].trim().slice(0, 1)) && !params) throw new CError('compile', '#define does not use \'=\': write #define ' + dm[1] + ' ' + dm[3].trim().slice(1).trim(), tk.line, tk.col);
          if (/;\s*$/.test(dm[3])) { /* allowed but suspicious; keep */ }
          macros[dm[1]] = { params: params, body: bodyToks };
        } else if (dir === 'undef') {
          delete macros[rest.trim()];
        }
        continue;
      }
      if (!active()) { idx++; continue; }
      if (tk.t === 'id' && macros[tk.v] && !(tk.hide && tk.hide[tk.v])) {
        var mac = macros[tk.v];
        var hide = Object.assign({}, tk.hide || {}); hide[tk.v] = true;
        var repl;
        if (mac.params) {
          if (!(input[idx + 1] && input[idx + 1].t === 'op' && input[idx + 1].v === '(')) { out.push(tk); idx++; continue; }
          var args = [[]], depth = 0, j = idx + 2;
          for (; j < input.length; j++) {
            var a = input[j];
            if (a.t === 'eof') throw new CError('compile', 'unterminated call to macro ' + tk.v, tk.line, tk.col);
            if (a.t === 'op' && a.v === '(') depth++;
            if (a.t === 'op' && a.v === ')') { if (depth === 0) break; depth--; }
            if (a.t === 'op' && a.v === ',' && depth === 0) { args.push([]); continue; }
            args[args.length - 1].push(a);
          }
          if (mac.params.length === 0 && args.length === 1 && args[0].length === 0) args = [];
          if (args.length !== mac.params.length) throw new CError('compile', 'macro ' + tk.v + ' expects ' + mac.params.length + ' arguments, got ' + args.length, tk.line, tk.col);
          repl = [];
          mac.body.forEach(function (bt) {
            var pi = bt.t === 'id' ? mac.params.indexOf(bt.v) : -1;
            if (pi >= 0) args[pi].forEach(function (at) { repl.push(at); });
            else repl.push(bt);
          });
          idx = j + 1;
        } else {
          repl = mac.body; idx++;
        }
        var mapped = repl.map(function (bt) {
          var c2 = Object.assign({}, bt);
          c2.line = tk.line; c2.col = tk.col; c2.s = tk.s; c2.e = tk.e;
          c2.hide = Object.assign({}, bt.hide || {}, hide);
          return c2;
        });
        input.splice.apply(input, [idx, 0].concat(mapped));
        continue;
      }
      out.push(tk); idx++;
    }
    return { toks: out, includes: includes };
  }

  // ------------------------------------------------------------------ types
  function IT(name, size, signed) { return { k: 'int', name: name, size: size, align: size, signed: signed }; }
  var T = {
    void: { k: 'void', name: 'void', size: 1, align: 1 },
    char: IT('char', 1, true), uchar: IT('unsigned char', 1, false),
    short: IT('short', 2, true), ushort: IT('unsigned short', 2, false),
    int: IT('int', 4, true), uint: IT('unsigned int', 4, false),
    long: IT('long', 8, true), ulong: IT('unsigned long', 8, false),
    bool: { k: 'int', name: 'bool', size: 1, align: 1, signed: false, isBool: true },
    float: { k: 'float', name: 'float', size: 4, align: 4 },
    double: { k: 'float', name: 'double', size: 8, align: 8 },
    file: { k: 'struct', tag: '_FILE', name: 'FILE', fields: [], size: 8, align: 8, complete: true, opaque: true }
  };
  function ptrT(t) { return { k: 'ptr', to: t, size: 8, align: 8 }; }
  function arrT(t, n) { return { k: 'arr', of: t, len: n, size: n == null ? 0 : n * t.size, align: t.align }; }
  function isInt(t) { return t.k === 'int'; }
  function isFlt(t) { return t.k === 'float'; }
  function isArith(t) { return t.k === 'int' || t.k === 'float'; }
  function isPtr(t) { return t.k === 'ptr'; }
  function isScalar(t) { return isArith(t) || isPtr(t); }
  function alignUp(x, a) { return Math.ceil(x / a) * a; }
  function typeStr(t) {
    switch (t.k) {
      case 'void': case 'int': case 'float': return t.name;
      case 'struct': return t.opaque ? 'FILE' : 'struct ' + (t.tag || '(anonymous)');
      case 'ptr':
        if (t.to.k === 'arr') return typeStr(t.to.of) + ' (*)[' + (t.to.len == null ? '' : t.to.len) + ']';
        return typeStr(t.to) + (t.to.k === 'ptr' ? '*' : ' *');
      case 'arr': {
        var dims = '', u = t; while (u.k === 'arr') { dims += '[' + (u.len == null ? '' : u.len) + ']'; u = u.of; }
        return typeStr(u) + ' ' + dims;
      }
      case 'func': return typeStr(t.ret) + ' (' + t.params.map(typeStr).join(', ') + ')';
    }
    return '?';
  }
  function sameType(a, b) {
    if (a === b) return true;
    if (a.k !== b.k) return false;
    switch (a.k) {
      case 'int': return a.size === b.size && a.signed === b.signed && !!a.isBool === !!b.isBool;
      case 'float': return a.size === b.size;
      case 'void': return true;
      case 'ptr': return sameType(a.to, b.to);
      case 'arr': return (a.len == null || b.len == null || a.len === b.len) && sameType(a.of, b.of);
      case 'struct': return a === b;
      case 'func': return false;
    }
    return false;
  }

  // ------------------------------------------------------------------ parser
  function Parser(toks, src) {
    this.toks = toks; this.pos = 0; this.src = src;
    this.typedefs = [{ FILE: T.file, size_t: T.ulong, ssize_t: T.long, uint8_t: T.uchar, int8_t: T.char, int16_t: T.short, uint16_t: T.ushort, int32_t: T.int, uint32_t: T.uint, int64_t: T.long, uint64_t: T.ulong, time_t: T.long }];
    this.structs = {};
    this.enumConsts = {};
    this.varScopes = [{}];
    this.warnings = [];
  }
  var P = Parser.prototype;
  P.peek = function (o) { return this.toks[this.pos + (o || 0)]; };
  P.next = function () { return this.toks[this.pos++]; };
  P.prev = function () { return this.toks[this.pos - 1]; };
  P.is = function (v, o) { var t = this.peek(o); return (t.t === 'op' || t.t === 'kw') && t.v === v; };
  P.accept = function (v) { if (this.is(v)) { return this.next(); } return null; };
  P.fail = function (msg, tok) { tok = tok || this.peek(); throw new CError('compile', msg, tok.line, tok.col); };
  P.expect = function (v, what) {
    if (this.is(v)) return this.next();
    var t = this.peek();
    var got = t.t === 'eof' ? 'end of file' : "'" + (t.t === 'str' ? '"..."' : t.v) + "'";
    if (v === ';') {
      var pt = this.prev();
      throw new CError('compile', "expected ';' after " + (what || 'statement') + ' (found ' + got + ')', pt.line, pt.col + (pt.e - pt.s));
    }
    this.fail("expected '" + v + "'" + (what ? ' ' + what : '') + ' but found ' + got);
  };
  P.lookupTypedef = function (name) {
    for (var i = this.typedefs.length - 1; i >= 0; i--) if (Object.prototype.hasOwnProperty.call(this.typedefs[i], name)) return this.typedefs[i][name];
    return null;
  };
  P.isTypeStart = function (tok) {
    tok = tok || this.peek();
    if (tok.t === 'kw') return /^(int|char|short|long|float|double|void|unsigned|signed|struct|union|enum|const|volatile|static|extern|register|inline|_Bool|bool|typedef|auto|restrict)$/.test(tok.v);
    if (tok.t === 'id') return !!this.lookupTypedef(tok.v) && !this.shadowed(tok.v);
    return false;
  };
  P.varNames = [{}];
  P.shadowed = function (name) {
    for (var i = this.varScopes.length - 1; i >= 0; i--) {
      if (this.varScopes[i][name] === 'var') return true;
      if (this.varScopes[i][name] === 'type') return false;
    }
    return false;
  };
  P.markVar = function (name) { this.varScopes[this.varScopes.length - 1][name] = 'var'; };
  P.markType = function (name) { this.varScopes[this.varScopes.length - 1][name] = 'type'; };

  P.parseSpecifiers = function (allowStorage) {
    var startTok = this.peek();
    var res = { type: null, isTypedef: false, isStatic: false };
    var counts = { signed: 0, unsigned: 0, short: 0, long: 0, int: 0, char: 0, float: 0, double: 0, void: 0, bool: 0 };
    var any = false, base = null;
    while (true) {
      var t = this.peek();
      if (t.t === 'kw') {
        if (/^(const|volatile|extern|register|inline|auto|restrict)$/.test(t.v)) { this.next(); any = true; continue; }
        if (t.v === 'static') { this.next(); res.isStatic = true; any = true; continue; }
        if (t.v === 'typedef') { this.next(); res.isTypedef = true; any = true; continue; }
        if (t.v === 'struct' || t.v === 'union') { if (base) this.fail('two data types in declaration'); this.next(); base = this.parseStruct(t); any = true; continue; }
        if (t.v === 'enum') { if (base) this.fail('two data types in declaration'); this.next(); base = this.parseEnum(); any = true; continue; }
        var key = t.v === '_Bool' ? 'bool' : t.v;
        if (Object.prototype.hasOwnProperty.call(counts, key)) { this.next(); counts[key]++; any = true; continue; }
        break;
      }
      if (t.t === 'id' && !base && !Object.keys(counts).some(function (k) { return counts[k] > 0; })) {
        var td = this.lookupTypedef(t.v);
        if (td && !this.shadowed(t.v)) { this.next(); base = td; any = true; continue; }
      }
      break;
    }
    if (!any) this.fail('expected a type');
    var basicUsed = Object.keys(counts).some(function (k) { return counts[k] > 0; });
    if (base && basicUsed) this.fail('cannot combine with previous type', startTok);
    if (!base) {
      if (counts.void) base = T.void;
      else if (counts.bool) base = T.bool;
      else if (counts.float) base = T.float;
      else if (counts.double) base = T.double;
      else if (counts.char) base = counts.unsigned ? T.uchar : T.char;
      else if (counts.short) base = counts.unsigned ? T.ushort : T.short;
      else if (counts.long) base = counts.unsigned ? T.ulong : T.long;
      else if (counts.int || counts.signed || counts.unsigned) base = counts.unsigned ? T.uint : T.int;
      else this.fail('expected a type', startTok);
    }
    res.type = base;
    return res;
  };

  P.parseStruct = function (kwTok) {
    if (kwTok.v === 'union') this.fail('unions are not supported here', kwTok);
    var tag = null;
    if (this.peek().t === 'id') tag = this.next().v;
    if (this.accept('{')) {
      var st = tag ? this.structs[tag] : null;
      if (st && st.complete) this.fail("redefinition of 'struct " + tag + "'", kwTok);
      if (!st) { st = { k: 'struct', tag: tag, fields: [], size: 0, align: 1, complete: false }; if (tag) this.structs[tag] = st; }
      var fields = [];
      while (!this.accept('}')) {
        if (this.peek().t === 'eof') this.fail("expected '}' to end struct");
        var spec = this.parseSpecifiers(false);
        do {
          var d = this.parseDeclarator(spec.type, false);
          if (d.type.k === 'struct' && !d.type.complete) this.fail("field '" + d.name + "' has incomplete type 'struct " + d.type.tag + "' (did you mean a pointer: struct " + d.type.tag + " *" + d.name + "?)", d.tok);
          if (d.type.k === 'func') this.fail('struct fields cannot be functions', d.tok);
          if (d.type.k === 'arr' && d.type.len == null) this.fail('array field needs a size', d.tok);
          fields.forEach(function (f) { if (f.name === d.name) throw new CError('compile', "duplicate member '" + d.name + "'", d.tok.line, d.tok.col); });
          fields.push({ name: d.name, type: d.type });
        } while (this.accept(','));
        this.expect(';', 'struct member');
      }
      var off = 0, al = 1;
      fields.forEach(function (f) { off = alignUp(off, f.type.align); f.offset = off; off += f.type.size; al = Math.max(al, f.type.align); });
      st.fields = fields; st.size = alignUp(Math.max(off, 1), al); st.align = al; st.complete = true;
      return st;
    }
    if (!tag) this.fail("expected a struct name or '{'");
    if (!this.structs[tag]) this.structs[tag] = { k: 'struct', tag: tag, fields: [], size: 0, align: 1, complete: false };
    return this.structs[tag];
  };

  P.parseEnum = function () {
    if (this.peek().t === 'id') this.next();
    if (this.accept('{')) {
      var v = 0;
      while (!this.accept('}')) {
        var nt = this.next();
        if (nt.t !== 'id') this.fail('expected an enum constant name', nt);
        if (this.accept('=')) v = this.constEval(this.parseConditional());
        this.enumConsts[nt.v] = v; v++;
        this.markVar(nt.v);
        if (!this.accept(',')) { this.expect('}'); break; }
      }
    }
    return T.int;
  };

  P.constEval = function (node) {
    var self = this;
    function ev(n) {
      switch (n.k) {
        case 'num': return n.v;
        case 'id': if (Object.prototype.hasOwnProperty.call(self.enumConsts, n.name)) return self.enumConsts[n.name];
          throw new CError('compile', "'" + n.name + "' is not a constant: array sizes must be constants (use #define SIZE 10, or malloc for sizes known only at run time)", n.line, n.col);
        case 'unary':
          var v = ev(n.e);
          if (n.op === '-') return -v; if (n.op === '+') return v; if (n.op === '!') return v ? 0 : 1; if (n.op === '~') return ~v;
          break;
        case 'binary':
          var a = ev(n.l), b = ev(n.r);
          switch (n.op) {
            case '+': return a + b; case '-': return a - b; case '*': return a * b;
            case '/': if (b === 0) cerr('division by zero in constant', n); return Math.trunc(a / b);
            case '%': if (b === 0) cerr('division by zero in constant', n); return a % b;
            case '<<': return a << b; case '>>': return a >> b; case '&': return a & b; case '|': return a | b; case '^': return a ^ b;
            case '<': return +(a < b); case '>': return +(a > b); case '<=': return +(a <= b); case '>=': return +(a >= b);
            case '==': return +(a === b); case '!=': return +(a !== b); case '&&': return +(a && b); case '||': return +(a || b);
          }
          break;
        case 'cond': return ev(n.c) ? ev(n.a) : ev(n.b);
        case 'cast': return ev(n.e);
        case 'sizeofT': return n.type.size;
        case 'sizeofE': break;
      }
      throw new CError('compile', 'expression is not a compile-time constant', n.line, n.col);
    }
    return ev(node);
  };

  // returns {name, tok, type, paramNames}
  P.parseDeclarator = function (base, allowAbstract) {
    var t = base;
    while (this.accept('*')) {
      t = ptrT(t);
      while (this.is('const') || this.is('volatile') || this.is('restrict')) this.next();
    }
    if (this.is('(') && (this.is('*', 1))) this.fail('function pointers are not supported here');
    var nameTok = null;
    if (this.peek().t === 'id') nameTok = this.next();
    else if (!allowAbstract) {
      var pk = this.peek();
      if (pk.t === 'kw') this.fail("'" + pk.v + "' is a keyword and cannot be used as a name");
      this.fail('expected a name in declaration');
    }
    var suffixes = [];
    var paramNames = null, paramInfo = null;
    while (true) {
      if (this.is('[')) {
        var lb = this.next();
        if (this.accept(']')) { suffixes.push({ arr: null, tok: lb }); continue; }
        var e = this.parseAssign();
        this.expect(']');
        suffixes.push({ arr: e, tok: lb });
      } else if (this.is('(') && (nameTok || allowAbstract)) {
        this.next();
        var pr = this.parseParams();
        suffixes.push({ fn: pr });
        if (!paramInfo) paramInfo = pr;
      } else break;
    }
    for (var i = suffixes.length - 1; i >= 0; i--) {
      var s = suffixes[i];
      if (s.fn) {
        if (t.k === 'arr') this.fail('function cannot return an array');
        t = { k: 'func', ret: t, params: s.fn.types, names: s.fn.names, variadic: s.fn.variadic, unspecified: s.fn.unspecified, size: 1, align: 1 };
      } else {
        var len = null;
        if (s.arr) {
          len = this.constEval(s.arr);
          if (len <= 0) this.fail('array size must be greater than zero', s.tok);
        }
        if (t.k === 'struct' && !t.complete) this.fail("array has incomplete element type 'struct " + t.tag + "'", s.tok);
        if (t.k === 'void') this.fail('cannot declare an array of void', s.tok);
        t = arrT(t, len);
      }
    }
    return { name: nameTok ? nameTok.v : null, tok: nameTok || this.peek(), type: t, params: paramInfo };
  };

  P.parseParams = function () {
    var res = { types: [], names: [], toks: [], variadic: false, unspecified: false };
    if (this.accept(')')) { res.unspecified = true; return res; }
    if (this.is('void') && this.is(')', 1)) { this.next(); this.next(); return res; }
    while (true) {
      if (this.accept('...')) { res.variadic = true; this.expect(')'); break; }
      var spec = this.parseSpecifiers(false);
      var d = this.parseDeclarator(spec.type, true);
      var pt = d.type;
      if (pt.k === 'arr') pt = ptrT(pt.of);
      if (pt.k === 'func') this.fail('function pointers are not supported here', d.tok);
      if (pt.k === 'void') this.fail("parameter cannot have type 'void'", d.tok);
      res.types.push(pt); res.names.push(d.name); res.toks.push(d.tok);
      if (this.accept(')')) break;
      this.expect(',', 'between parameters');
    }
    return res;
  };

  P.parseTypeName = function () {
    var spec = this.parseSpecifiers(false);
    var d = this.parseDeclarator(spec.type, true);
    if (d.name) this.fail('unexpected name in type', d.tok);
    return d.type;
  };

  function mk(k, tok, props) { var n = props || {}; n.k = k; n.line = tok.line; n.col = tok.col; n.s = tok.s; return n; }
  P.fin = function (n) { n.ee = this.prev().e; return n; };

  P.parseExpr = function () {
    var st = this.peek();
    var e = this.parseAssign();
    while (this.is(',')) { this.next(); var r = this.parseAssign(); e = this.fin(mk('comma', st, { l: e, r: r })); }
    return e;
  };
  var ASSIGN_OPS = { '=': 1, '+=': 1, '-=': 1, '*=': 1, '/=': 1, '%=': 1, '<<=': 1, '>>=': 1, '&=': 1, '|=': 1, '^=': 1 };
  P.parseAssign = function () {
    var st = this.peek();
    var l = this.parseConditional();
    var t = this.peek();
    if (t.t === 'op' && ASSIGN_OPS[t.v]) {
      this.next();
      var r = this.parseAssign();
      return this.fin(mk('assign', st, { op: t.v, l: l, r: r, opTok: t }));
    }
    return l;
  };
  P.parseConditional = function () {
    var st = this.peek();
    var c = this.parseBinary(1);
    if (this.accept('?')) {
      var a = this.parseExpr();
      this.expect(':', "in '? :' expression");
      var b = this.parseConditional();
      return this.fin(mk('cond', st, { c: c, a: a, b: b }));
    }
    return c;
  };
  var PREC = { '||': 1, '&&': 2, '|': 3, '^': 4, '&': 5, '==': 6, '!=': 6, '<': 7, '>': 7, '<=': 7, '>=': 7, '<<': 8, '>>': 8, '+': 9, '-': 9, '*': 10, '/': 10, '%': 10 };
  P.parseBinary = function (minPrec) {
    var st = this.peek();
    var l = this.parseCast();
    while (true) {
      var t = this.peek();
      if (t.t !== 'op' || !PREC[t.v] || PREC[t.v] < minPrec) break;
      this.next();
      var r = this.parseBinary(PREC[t.v] + 1);
      l = this.fin(mk('binary', st, { op: t.v, l: l, r: r, opTok: t }));
    }
    return l;
  };
  P.parseCast = function () {
    var st = this.peek();
    if (this.is('(') && this.isTypeStart(this.peek(1))) {
      this.next();
      var ty = this.parseTypeName();
      this.expect(')', 'after type in cast');
      if (this.is('{')) this.fail('compound literals like (int[]){1, 2} are not supported here; declare an array variable instead');
      var e = this.parseCast();
      return this.fin(mk('cast', st, { type: ty, e: e }));
    }
    return this.parseUnary();
  };
  P.parseUnary = function () {
    var t = this.peek();
    if (t.t === 'op') {
      if (t.v === '++' || t.v === '--') { this.next(); var e = this.parseUnary(); return this.fin(mk('preinc', t, { op: t.v, e: e })); }
      if (t.v === '&' || t.v === '*' || t.v === '+' || t.v === '-' || t.v === '!' || t.v === '~') {
        this.next(); var e2 = this.parseCast(); return this.fin(mk('unary', t, { op: t.v, e: e2 }));
      }
    }
    if (t.t === 'kw' && t.v === 'sizeof') {
      this.next();
      if (this.is('(') && this.isTypeStart(this.peek(1))) {
        this.next(); var ty = this.parseTypeName(); this.expect(')');
        return this.fin(mk('sizeofT', t, { type: ty }));
      }
      var e3 = this.parseUnary();
      return this.fin(mk('sizeofE', t, { e: e3 }));
    }
    return this.parsePostfix();
  };
  P.parsePostfix = function () {
    var st = this.peek();
    var e = this.parsePrimary();
    while (true) {
      var t = this.peek();
      if (t.t !== 'op') break;
      if (t.v === '[') { this.next(); var i = this.parseExpr(); this.expect(']'); e = this.fin(mk('index', st, { a: e, i: i, tok: t })); continue; }
      if (t.v === '(') {
        this.next(); var args = [];
        if (!this.accept(')')) {
          while (true) { args.push(this.parseAssign()); if (this.accept(')')) break; this.expect(',', 'between arguments'); }
        }
        e = this.fin(mk('call', st, { f: e, args: args })); continue;
      }
      if (t.v === '.' || t.v === '->') {
        this.next(); var nt = this.next();
        if (nt.t !== 'id') this.fail("expected a field name after '" + t.v + "'", nt);
        e = this.fin(mk('member', st, { e: e, name: nt.v, arrow: t.v === '->', tok: nt })); continue;
      }
      if (t.v === '++' || t.v === '--') { this.next(); e = this.fin(mk('postinc', st, { op: t.v, e: e })); continue; }
      break;
    }
    return e;
  };
  P.parsePrimary = function () {
    var t = this.next();
    if (t.t === 'num') {
      var ty = t.isFloat ? T.double : t.isChar ? T.int : (t.isLong || t.v > 2147483647) ? (t.isUnsigned ? T.ulong : T.long) : (t.isUnsigned ? T.uint : T.int);
      if (!t.isFloat && !t.isLong && !t.isUnsigned && t.v > 2147483647 && t.v <= 4294967295 && t.s !== undefined) ty = T.long;
      return this.fin(mk('num', t, { v: t.v, type: ty }));
    }
    if (t.t === 'str') {
      var bytes = t.v.slice();
      while (this.peek().t === 'str') bytes = bytes.concat(this.next().v);
      return this.fin(mk('str', t, { bytes: bytes }));
    }
    if (t.t === 'id') {
      if (Object.prototype.hasOwnProperty.call(this.enumConsts, t.v) && !this.shadowedEnum(t.v)) return this.fin(mk('num', t, { v: this.enumConsts[t.v], type: T.int }));
      return this.fin(mk('id', t, { name: t.v }));
    }
    if (t.t === 'op' && t.v === '(') {
      var e = this.parseExpr();
      this.expect(')');
      return e;
    }
    var what = t.t === 'eof' ? 'end of file' : "'" + t.v + "'";
    throw new CError('compile', 'expected an expression but found ' + what, t.line, t.col);
  };
  P.shadowedEnum = function () { return false; };

  // ---- statements
  P.parseStatement = function () {
    var t = this.peek();
    if (t.t === 'op' && t.v === '{') return this.parseBlock();
    if (t.t === 'op' && t.v === ';') { this.next(); return mk('empty', t); }
    if (t.t === 'kw') {
      switch (t.v) {
        case 'if': {
          this.next(); this.expect('(', "after 'if'"); var c = this.parseExpr(); this.expect(')', 'after if condition');
          if (this.is(';')) { var semi = this.peek(); this.warn("empty body after 'if (...)': the ';' ends the if statement", semi); }
          var th = this.parseStatement(); var el = null;
          if (this.accept('else')) el = this.parseStatement();
          return mk('if', t, { c: c, t: th, f: el });
        }
        case 'while': {
          this.next(); this.expect('(', "after 'while'"); var c2 = this.parseExpr(); this.expect(')', 'after while condition');
          if (this.is(';')) this.warn("empty body after 'while (...)': this is an infinite loop if the condition stays true", this.peek());
          var body = this.parseLoopBody();
          return mk('while', t, { c: c2, body: body });
        }
        case 'do': {
          this.next(); var b = this.parseLoopBody(); this.expect('while', "after do-loop body"); this.expect('(');
          var c3 = this.parseExpr(); this.expect(')'); this.expect(';', 'do-while loop');
          return mk('do', t, { c: c3, body: b });
        }
        case 'for': {
          this.next(); this.expect('(', "after 'for'");
          this.varScopes.push({});
          var init = null;
          if (this.accept(';')) init = null;
          else if (this.isTypeStart()) init = this.parseDeclaration(false);
          else { init = mk('expr', this.peek(), { e: this.parseExpr() }); this.expect(';', 'for-loop initialisation'); }
          var cond = this.is(';') ? null : this.parseExpr();
          this.expect(';', 'for-loop condition');
          var step = this.is(')') ? null : this.parseExpr();
          this.expect(')', 'to close the for (...)');
          if (this.is(';')) this.warn("empty body after 'for (...)': the ';' is the whole loop body", this.peek());
          var fb = this.parseLoopBody();
          this.varScopes.pop();
          return mk('for', t, { init: init, c: cond, step: step, body: fb });
        }
        case 'return': {
          this.next(); var e = null;
          if (!this.is(';')) e = this.parseExpr();
          this.expect(';', 'return statement');
          return mk('return', t, { e: e });
        }
        case 'break': this.next(); this.expect(';', "'break'"); return mk('break', t);
        case 'continue': this.next(); this.expect(';', "'continue'"); return mk('continue', t);
        case 'switch': {
          this.next(); this.expect('(', "after 'switch'"); var se = this.parseExpr(); this.expect(')');
          this.switchDepth = (this.switchDepth || 0) + 1;
          var sb = this.parseStatement();
          this.switchDepth--;
          return mk('switch', t, { e: se, body: sb });
        }
        case 'case': {
          this.next(); if (!this.switchDepth) this.fail("'case' label not inside a switch", t);
          var ce = this.parseConditional(); this.expect(':', 'after case value');
          return mk('case', t, { e: ce });
        }
        case 'default': this.next(); this.expect(':', "after 'default'"); if (!this.switchDepth) this.fail("'default' label not inside a switch", t); return mk('default', t);
        case 'goto': this.fail('goto is not supported here', t); break;
        case 'else': this.fail("'else' without a matching 'if' (check your braces { })", t); break;
      }
    }
    if (this.isTypeStart()) return this.parseDeclaration(false);
    var st = this.peek();
    var ex = this.parseExpr();
    this.expect(';');
    return mk('expr', st, { e: ex });
  };
  P.parseLoopBody = function () {
    this.loopDepth = (this.loopDepth || 0) + 1;
    var b = this.parseStatement();
    this.loopDepth--;
    return b;
  };
  P.warn = function (msg, tok) { this.warnings.push({ msg: msg, line: tok.line, col: tok.col }); };
  P.parseBlock = function () {
    var t = this.expect('{');
    this.varScopes.push({});
    this.typedefs.push({});
    var items = [];
    while (!this.is('}')) {
      if (this.peek().t === 'eof') this.fail("expected '}' (a '{' was never closed)", t);
      items.push(this.parseStatement());
    }
    this.next();
    this.varScopes.pop();
    this.typedefs.pop();
    return mk('block', t, { items: items });
  };

  P.parseInitializer = function () {
    var st = this.peek();
    if (this.accept('{')) {
      var items = [];
      while (!this.accept('}')) {
        var desig = [];
        while (this.is('.') || this.is('[')) {
          if (this.accept('.')) { var nt = this.next(); if (nt.t !== 'id') this.fail('expected field name', nt); desig.push({ field: nt.v, tok: nt }); }
          else { this.next(); var ie = this.parseConditional(); this.expect(']'); desig.push({ index: this.constEval(ie), tok: st }); }
        }
        if (desig.length) this.expect('=', 'after designator');
        var v = this.parseInitializer();
        items.push({ desig: desig, v: v });
        if (!this.accept(',')) { this.expect('}', 'to end initializer list'); break; }
      }
      return this.fin(mk('initlist', st, { items: items }));
    }
    return this.parseAssign();
  };

  // declaration statement (local or global). Returns 'decl' node.
  P.parseDeclaration = function (isGlobal, preSpec, preDecl, preTok) {
    var st = preTok || this.peek();
    var spec = preSpec || this.parseSpecifiers(true);
    var decls = [];
    if (!preDecl && this.accept(';')) return mk('decl', st, { decls: decls, spec: spec });
    do {
      var d = preDecl || this.parseDeclarator(spec.type, false);
      preDecl = null;
      if (spec.isTypedef) {
        this.typedefs[this.typedefs.length - 1][d.name] = d.type;
        this.markType(d.name);
        continue;
      }
      var init = null;
      if (this.accept('=')) init = this.parseInitializer();
      if (d.type.k !== 'func') this.markVar(d.name);
      decls.push({ name: d.name, tok: d.tok, type: d.type, init: init, isStatic: spec.isStatic, params: d.params });
    } while (this.accept(','));
    this.expect(';', 'declaration');
    return mk('decl', st, { decls: decls, spec: spec });
  };

  P.parseProgram = function () {
    this.varScopes = [{}];
    this.warnings = [];
    var items = [];
    while (this.peek().t !== 'eof') {
      if (this.accept(';')) continue;
      var st = this.peek();
      if (!this.isTypeStart()) {
        if (st.t === 'id' && this.is('(', 1)) this.fail("missing return type for function '" + st.v + "' (write: int " + st.v + "(...))", st);
        this.fail('expected a declaration or function definition', st);
      }
      // try function definition
      var save = this.pos;
      var spec = this.parseSpecifiers(true);
      if (this.accept(';')) continue;
      var d = this.parseDeclarator(spec.type, false);
      if (d.type.k === 'func' && this.is('{')) {
        if (spec.isTypedef) this.fail('typedef cannot have a function body');
        var fnTok = d.tok;
        this.varScopes.push({});
        (d.params ? d.params.names : []).forEach(function (nm) { if (nm) this.markVar(nm); }, this);
        if (d.params) d.params.names.forEach(function (nm, i) { if (!nm) throw new CError('compile', 'parameter ' + (i + 1) + ' of ' + d.name + ' needs a name', d.params.toks[i].line, d.params.toks[i].col); });
        var body = this.parseBlock();
        this.varScopes.pop();
        items.push(mk('func', fnTok, { name: d.name, type: d.type, paramNames: d.params ? d.params.names : [], paramToks: d.params ? d.params.toks : [], body: body }));
        continue;
      }
      items.push(this.parseDeclaration(true, spec, d, st));
    }
    return items;
  };

  // ------------------------------------------------------------------ machine
  var MEM = 24 << 20;
  var GLOBAL_BASE = 4096, STACK_BASE = 2 << 20, STACK_END = 10 << 20, HEAP_BASE = 10 << 20;
  var NORMAL = 0, BRK = 1, CONT = 2, RET = 3;

  var buf, DV, U8, IB, SH, R_START, R_END, R_KIND, R_LINE, R_DESC, R_FREEDLINE, R_RO, R_TYPE;
  var nRegions, freeStackIds, gTop, sTop, hTop;
  var LINE, STEPS, STEP_LIMIT, OUT, ERR, INPUT, INPOS, OUT_LIMIT, CALL_DEPTH, RETV, FP, SRC_LINES, RAND_STATE;

  function resetMachine() {
    if (!buf) {
      buf = new ArrayBuffer(MEM); DV = new DataView(buf); U8 = new Uint8Array(buf);
      IB = new Uint8Array(MEM); SH = new Int32Array(MEM >> 3);
    } else {
      U8.fill(0); IB.fill(0); SH.fill(0);
    }
    R_START = [0]; R_END = [0]; R_KIND = ['']; R_LINE = [0]; R_DESC = ['']; R_FREEDLINE = [0]; R_RO = [0]; R_TYPE = [null];
    nRegions = 1; freeStackIds = [];
    gTop = GLOBAL_BASE; sTop = STACK_BASE; hTop = HEAP_BASE;
    STEPS = 0; OUT = []; ERR = []; INPOS = 0; CALL_DEPTH = 0; RETV = 0; FP = STACK_BASE; RAND_STATE = 1;
  }

  function rt(msg) { throw new CError('runtime', msg, LINE, 0); }

  function newRegion(start, size, kind, desc, line, type) {
    var id;
    if (kind === 'stack' && freeStackIds.length) id = freeStackIds.pop();
    else { id = nRegions++; }
    R_START[id] = start; R_END[id] = start + size; R_KIND[id] = kind; R_LINE[id] = line; R_DESC[id] = desc; R_FREEDLINE[id] = 0; R_RO[id] = 0; R_TYPE[id] = type || null;
    var g0 = start >> 3, g1 = (start + Math.max(size, 1) - 1) >> 3;
    for (var g = g0; g <= g1; g++) SH[g] = id;
    return id;
  }
  function killRegion(id, freedLine) {
    var g0 = R_START[id] >> 3, g1 = (R_START[id] + Math.max(R_END[id] - R_START[id], 1) - 1) >> 3;
    for (var g = g0; g <= g1; g++) SH[g] = -id;
    R_FREEDLINE[id] = freedLine;
  }
  function allocGlobal(size, align, desc, ro, type) {
    var start = alignUp(gTop, Math.max(8, align));
    if (start + size + 16 > STACK_BASE) cerr('too much global data');
    var id = newRegion(start, size, ro ? 'string' : 'global', desc, 0, type);
    R_RO[id] = ro ? 1 : 0;
    gTop = start + size + 16;
    return start;
  }

  function describeBad(a, n, id) {
    if (id < 0) {
      var k = -id;
      if (R_KIND[k] === 'heap') return 'use of memory after it was freed (malloc at line ' + R_LINE[k] + ', free at line ' + R_FREEDLINE[k] + ')';
      if (R_KIND[k] === 'stack') return 'use of ' + R_DESC[k] + ' after its function returned (do not return the address of a local variable)';
      return 'invalid memory access';
    }
    // find nearest region below
    for (var g = (a >> 3), steps = 0; g >= 0 && steps < 4096; g--, steps++) {
      var j = SH[g];
      if (j > 0) {
        var past = a - R_END[j];
        if (past >= 0) return 'access ' + (past === 0 ? 'just' : past + ' byte' + (past === 1 ? '' : 's')) + ' past the end of ' + regionName(j) + ' (out of bounds)';
        break;
      }
      if (j < 0) break;
    }
    return 'out of bounds memory access (the address is not inside any variable or malloc\'d block)';
  }
  function regionName(id) {
    if (R_KIND[id] === 'heap') return 'a ' + (R_END[id] - R_START[id]) + '-byte block malloc\'d at line ' + R_LINE[id];
    if (R_KIND[id] === 'string') return 'a string literal';
    return R_DESC[id];
  }
  function chk(a, n, w) {
    if (a < 4096) {
      if (a >= 0 && a < 4096) rt(a === 0 ? 'NULL pointer dereferenced' : 'pointer near NULL dereferenced (a field accessed through a NULL pointer?)');
      rt('invalid pointer');
    }
    if (a >= MEM || a !== Math.floor(a)) rt('invalid pointer (address out of range)');
    var id = SH[a >> 3];
    if (id <= 0) rt(describeBad(a, n, id));
    if (a + n > R_END[id]) { var past = a - R_END[id]; rt(past >= 0 ? 'access ' + (past === 0 ? 'just' : past + ' byte' + (past === 1 ? '' : 's')) + ' past the end of ' + regionName(id) + ' (out of bounds)' : 'access runs past the end of ' + regionName(id) + ' (out of bounds)'); }
    if (w && R_RO[id]) rt('cannot modify a string literal (copy it into a char array first)');
  }
  function uninit(a) {
    var id = SH[a >> 3];
    if (id > 0 && R_KIND[id] === 'heap') rt('value read from malloc\'d memory before it was set (block malloc\'d at line ' + R_LINE[id] + ')');
    if (id > 0) rt('uninitialized value used: ' + R_DESC[id] + ' was read before it was given a value');
    rt('uninitialized value used');
  }
  function setInit(a, n) { for (var i = 0; i < n; i++) IB[a + i] = 1; }

  // typed load/store
  function loader(t) {
    if (t.k === 'int') {
      switch (t.size) {
        case 1: return t.signed ? function (a) { chk(a, 1, 0); if (!IB[a]) uninit(a); return DV.getInt8(a); } : function (a) { chk(a, 1, 0); if (!IB[a]) uninit(a); return DV.getUint8(a); };
        case 2: return t.signed ? function (a) { chk(a, 2, 0); if (!IB[a]) uninit(a); return DV.getInt16(a, true); } : function (a) { chk(a, 2, 0); if (!IB[a]) uninit(a); return DV.getUint16(a, true); };
        case 4: return t.signed ? function (a) { chk(a, 4, 0); if (!IB[a]) uninit(a); return DV.getInt32(a, true); } : function (a) { chk(a, 4, 0); if (!IB[a]) uninit(a); return DV.getUint32(a, true); };
        case 8: return function (a) { chk(a, 8, 0); if (!IB[a]) uninit(a); return DV.getFloat64(a, true); };
      }
    }
    if (t.k === 'float') return t.size === 4 ? function (a) { chk(a, 4, 0); if (!IB[a]) uninit(a); return DV.getFloat32(a, true); } : function (a) { chk(a, 8, 0); if (!IB[a]) uninit(a); return DV.getFloat64(a, true); };
    if (t.k === 'ptr') return function (a) { chk(a, 8, 0); if (!IB[a]) uninit(a); return DV.getFloat64(a, true); };
    throw new Error('no loader for ' + typeStr(t));
  }
  function storer(t) {
    if (t.k === 'int') {
      switch (t.size) {
        case 1: return function (a, v) { chk(a, 1, 1); DV.setInt8(a, v); IB[a] = 1; };
        case 2: return function (a, v) { chk(a, 2, 1); DV.setInt16(a, v, true); IB[a] = IB[a + 1] = 1; };
        case 4: return function (a, v) { chk(a, 4, 1); DV.setInt32(a, v, true); IB[a] = IB[a + 1] = IB[a + 2] = IB[a + 3] = 1; };
        case 8: return function (a, v) { chk(a, 8, 1); DV.setFloat64(a, v, true); setInit(a, 8); };
      }
    }
    if (t.k === 'float') return t.size === 4 ? function (a, v) { chk(a, 4, 1); DV.setFloat32(a, v, true); setInit(a, 4); } : function (a, v) { chk(a, 8, 1); DV.setFloat64(a, v, true); setInit(a, 8); };
    if (t.k === 'ptr') return function (a, v) { chk(a, 8, 1); DV.setFloat64(a, v, true); setInit(a, 8); };
    throw new Error('no storer for ' + typeStr(t));
  }
  function memcopy(dst, src, n) {
    if (n <= 0) return;
    chk(src, n, 0); chk(dst, n, 1);
    U8.copyWithin(dst, src, src + n); IB.copyWithin(dst, src, src + n);
  }
  function readCStr(a, what) {
    if (a === 0) rt((what || 'string function') + ': NULL pointer passed as a string');
    var bytes = [];
    while (true) {
      chk(a, 1, 0);
      if (!IB[a]) rt((what || 'string') + ': reading a string that is not terminated with \'\\0\' (hit uninitialized memory) - did you forget to add \'\\0\' at the end?');
      var b = U8[a];
      if (b === 0) return bytes;
      bytes.push(b); a++;
      if (bytes.length > 10000000) rt('string too long');
    }
  }
  function writeBytes(a, bytes, what) {
    for (var i = 0; i < bytes.length; i++) {
      var id = SH[(a + i) >> 3];
      if (a + i < 4096) rt((what || 'write') + ': NULL pointer');
      if (id <= 0 || a + i >= R_END[id]) rt((what || 'write') + ': writing past the end of ' + (id > 0 ? regionName(id) : id < 0 ? regionName(-id) : 'the buffer') + ' (buffer too small)');
      if (R_RO[id]) rt('cannot modify a string literal');
      U8[a + i] = bytes[i]; IB[a + i] = 1;
    }
  }
  function bytesToStr(bytes) {
    try { return new TextDecoder('utf-8').decode(new Uint8Array(bytes)); } catch (e) { return String.fromCharCode.apply(null, bytes); }
  }

  // conversions
  function convFn(from, to) {
    if (to.k === 'void') return function () { return 0; };
    if (to.k === 'int') {
      var wrap;
      if (to.isBool) wrap = function (v) { return v ? 1 : 0; };
      else if (to.size === 1) wrap = to.signed ? function (v) { return (v << 24) >> 24; } : function (v) { return v & 255; };
      else if (to.size === 2) wrap = to.signed ? function (v) { return (v << 16) >> 16; } : function (v) { return v & 65535; };
      else if (to.size === 4) wrap = to.signed ? function (v) { return v | 0; } : function (v) { return v >>> 0; };
      else wrap = function (v) { return v; };
      if (from.k === 'float' && !to.isBool) return function (v) { if (v !== v || v === Infinity || v === -Infinity) return 0; return wrap(Math.trunc(v)); };
      return wrap;
    }
    if (to.k === 'float') return to.size === 4 ? function (v) { return Math.fround(v); } : function (v) { return v; };
    return function (v) { return v; };
  }

  // ------------------------------------------------------------------ compiler
  function Compiler(parser, src, includes) {
    this.p = parser; this.src = src; this.includes = includes;
    this.globals = {};    // name -> sym
    this.funcs = {};      // name -> F
    this.strPool = {};
    this.staticInits = [];
    this.globalInits = [];
    this.scope = null;
    this.fn = null;
    this.loopDepth = 0; this.switchDepth = 0;
  }
  var C = Compiler.prototype;
  C.text = function (n) { return n && n.s != null && n.ee != null ? this.src.slice(n.s, n.ee) : ''; };
  C.lookup = function (name) {
    for (var s = this.scope; s; s = s.parent) if (Object.prototype.hasOwnProperty.call(s.vars, name)) return s.vars[name];
    if (Object.prototype.hasOwnProperty.call(this.globals, name)) return this.globals[name];
    if (Object.prototype.hasOwnProperty.call(this.funcs, name)) return { kind: 'func', F: this.funcs[name] };
    return null;
  };

  C.strLiteral = function (bytes) {
    var key = bytes.join(',');
    if (this.strPool[key] !== undefined) return this.strPool[key];
    var a = allocGlobal(bytes.length + 1, 1, 'a string literal', true, arrT(T.char, bytes.length + 1));
    for (var i = 0; i < bytes.length; i++) { U8[a + i] = bytes[i]; IB[a + i] = 1; }
    U8[a + bytes.length] = 0; IB[a + bytes.length] = 1;
    this.strPool[key] = a;
    return a;
  };

  // E: {t, get, addr, lv, cnst, isNull, node}
  function E(t, get, props) { var e = props || {}; e.t = t; e.get = get; return e; }

  C.decay = function (e) {
    if (e.t.k === 'arr') { var a = e.addr; return E(ptrT(e.t.of), a, { node: e.node, fromArr: e.t }); }
    if (e.t.k === 'func') cerr("function '" + (e.fname || '') + "' used without calling it (add parentheses: " + (e.fname || 'f') + '(...))', e.node);
    return e;
  };
  C.rvalue = function (node) {
    var e = this.decay(this.expr(node));
    return e;
  };
  C.truthy = function (node) {
    var e = this.rvalue(node);
    if (e.t.k === 'struct') cerr('a struct cannot be used as a condition', node);
    if (e.t.k === 'void') cerr('void value used as a condition', node);
    var g = e.get;
    if (node.k === 'assign' && node.op === '=' && !node.parens) this.warn("assignment used as a condition: did you mean '==' instead of '='?", node);
    return function () { return g() ? 1 : 0; };
  };
  C.warn = function (msg, node) { this.warnings.push({ msg: msg, line: node.line, col: node.col }); };

  C.checkAssign = function (to, e, node, what) {
    var from = e.t;
    if (to.k === 'ptr') {
      if (from.k === 'ptr') {
        if (to.to.k === 'void' || from.to.k === 'void') return;
        if (sameType(to.to, from.to)) return;
        if (to.to.k === 'int' && from.to.k === 'int' && to.to.size === 1 && from.to.size === 1) return;
        cerr('incompatible pointer types: ' + what + " '" + typeStr(to) + "' from '" + typeStr(from) + "'", node);
      }
      if (from.k === 'int') {
        if (e.isNull || e.cnst === 0) return;
        cerr('cannot ' + what + " pointer '" + typeStr(to) + "' from integer '" + typeStr(from) + "' (did you forget * or &?)", node);
      }
      cerr('cannot ' + what + " '" + typeStr(to) + "' from '" + typeStr(from) + "'", node);
    }
    if (to.k === 'int' || to.k === 'float') {
      if (from.k === 'ptr') {
        if (to.isBool) return;
        cerr('cannot ' + what + " '" + typeStr(to) + "' from pointer '" + typeStr(from) + "' (did you forget to dereference with * or ->?)", node);
      }
      if (from.k === 'struct') cerr('cannot ' + what + " '" + typeStr(to) + "' from '" + typeStr(from) + "'", node);
      if (from.k === 'void') cerr('void value cannot be used', node);
      return;
    }
    if (to.k === 'struct') {
      if (from !== to) cerr('cannot ' + what + " '" + typeStr(to) + "' from '" + typeStr(from) + "'", node);
      return;
    }
  };

  // usual arithmetic conversions
  function arithType(a, b) {
    if (a.k === 'float' || b.k === 'float') return T.double;
    var sa = a.size, sb = b.size;
    if (sa === 8 || sb === 8) { if ((sa === 8 && !a.signed) || (sb === 8 && !b.signed)) return T.ulong; return T.long; }
    if ((sa === 4 && !a.signed) || (sb === 4 && !b.signed)) return T.uint;
    return T.int;
  }
  function promote(t) { if (t.k === 'int' && t.size < 4) return T.int; return t; }

  C.expr = function (n) {
    var self = this;
    switch (n.k) {
      case 'num': {
        var v = n.v; return E(n.type, function () { return v; }, { cnst: v, node: n });
      }
      case 'str': {
        var a = this.strLiteral(n.bytes);
        var at = arrT(T.char, n.bytes.length + 1);
        return E(at, function () { return a; }, { addr: function () { return a; }, lv: false, node: n, isStr: true });
      }
      case 'id': {
        var sym = this.lookup(n.name);
        if (!sym) {
          if (BUILTINS[n.name]) cerr("'" + n.name + "' is a library function: call it with parentheses, e.g. " + n.name + '(...)', n);
          var hint = '';
          var near = this.nearName(n.name);
          if (near) hint = " (did you mean '" + near + "'?)";
          cerr("use of undeclared identifier '" + n.name + "'" + hint, n);
        }
        if (sym.kind === 'func') return E(sym.F.type, null, { fname: n.name, F: sym.F, node: n });
        var t = sym.type;
        var addrFn = sym.global ? (function (ga) { return function () { return ga; }; })(sym.addr) : (function (off) { return function () { return FP + off; }; })(sym.off);
        if (t.k === 'arr' || t.k === 'struct') return E(t, addrFn, { addr: addrFn, lv: true, node: n, varName: n.name });
        var ld = loader(t);
        var getFn = sym.global ? (function (ga) { return function () { return ld(ga); }; })(sym.addr) : (function (off) { return function () { return ld(FP + off); }; })(sym.off);
        return E(t, getFn, { addr: addrFn, lv: true, node: n, varName: n.name });
      }
      case 'unary': return this.unary(n);
      case 'preinc': case 'postinc': return this.incdec(n);
      case 'binary': return this.binary(n);
      case 'assign': return this.assign(n);
      case 'cond': {
        var c = this.truthy(n.c);
        var ea = this.rvalue(n.a), eb = this.rvalue(n.b);
        var rt2;
        if (isArith(ea.t) && isArith(eb.t)) rt2 = arithType(promote(ea.t), promote(eb.t));
        else if (isPtr(ea.t) && (isPtr(eb.t) || eb.isNull || eb.cnst === 0)) rt2 = ea.t;
        else if (isPtr(eb.t) && (ea.isNull || ea.cnst === 0)) rt2 = eb.t;
        else if (ea.t.k === 'void' && eb.t.k === 'void') rt2 = T.void;
        else if (ea.t.k === 'struct' && ea.t === eb.t) rt2 = ea.t;
        else cerr("the two sides of '? :' have different types ('" + typeStr(ea.t) + "' and '" + typeStr(eb.t) + "')", n);
        var ca = convFn(ea.t, rt2), cb = convFn(eb.t, rt2), ga = ea.get, gb = eb.get;
        return E(rt2, function () { return c() ? ca(ga()) : cb(gb()); }, { node: n });
      }
      case 'comma': {
        var l = this.rvalue(n.l), r = this.rvalue(n.r), gl = l.get, gr = r.get;
        return E(r.t, function () { gl(); return gr(); }, { node: n });
      }
      case 'cast': {
        var e = this.rvalue(n.e), to = n.type;
        if (to.k === 'void') { var g0 = e.get; return E(T.void, function () { g0(); return 0; }, { node: n }); }
        if (to.k === 'struct' || to.k === 'arr') cerr("cannot cast to '" + typeStr(to) + "'", n);
        if (e.t.k === 'struct') cerr("cannot cast a struct to '" + typeStr(to) + "'", n);
        if (to.k === 'ptr' && e.t.k === 'float') cerr('cannot cast a floating-point value to a pointer', n);
        if (to.k === 'float' && e.t.k === 'ptr') cerr('cannot cast a pointer to a floating-point type', n);
        var cv = convFn(e.t, to), g = e.get;
        var res = E(to, function () { return cv(g()); }, { node: n });
        if (e.cnst !== undefined && to.k !== 'ptr') res.cnst = cv(e.cnst);
        if (to.k === 'ptr' && (e.isNull || e.cnst === 0)) res.isNull = true;
        return res;
      }
      case 'sizeofT': {
        if (n.type.k === 'struct' && !n.type.complete) cerr("sizeof applied to incomplete type 'struct " + n.type.tag + "'", n);
        if (n.type.k === 'arr' && n.type.len == null) cerr('sizeof of an array with unknown size', n);
        var sz = n.type.size; return E(T.ulong, function () { return sz; }, { cnst: sz, node: n });
      }
      case 'sizeofE': {
        var se = this.expr(n.e);
        if (se.t.k === 'func') cerr('sizeof of a function', n);
        if (se.t.k === 'struct' && !se.t.complete) cerr('sizeof of incomplete type', n);
        var sz2 = se.t.size; return E(T.ulong, function () { return sz2; }, { cnst: sz2, node: n });
      }
      case 'call': return this.call(n);
      case 'index': return this.index(n);
      case 'member': return this.member(n);
      case 'initlist': cerr('a { ... } list can only be used to initialise a variable in its declaration', n);
    }
    cerr('unsupported expression (' + n.k + ')', n);
  };

  C.nearName = function (name) {
    var names = Object.keys(this.globals).concat(Object.keys(this.funcs));
    for (var s = this.scope; s; s = s.parent) names = names.concat(Object.keys(s.vars));
    var best = null, bd = 3;
    names.forEach(function (m) { var d = editDist(name.toLowerCase(), m.toLowerCase()); if (d < bd) { bd = d; best = m; } });
    return best;
  };
  function editDist(a, b) {
    if (Math.abs(a.length - b.length) > 2) return 9;
    var dp = []; for (var i = 0; i <= a.length; i++) { dp[i] = [i]; }
    for (var j = 1; j <= b.length; j++) dp[0][j] = j;
    for (i = 1; i <= a.length; i++) for (j = 1; j <= b.length; j++) dp[i][j] = Math.min(dp[i - 1][j] + 1, dp[i][j - 1] + 1, dp[i - 1][j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
    return dp[a.length][b.length];
  }

  C.unary = function (n) {
    var op = n.op, self = this;
    if (op === '&') {
      var e = this.expr(n.e);
      if (e.t.k === 'func') cerr('function pointers are not supported here', n);
      if (!e.addr) cerr("cannot take the address of '" + this.text(n.e) + "' (it is not a variable)", n);
      var af = e.addr;
      return E(ptrT(e.t), af, { node: n });
    }
    if (op === '*') {
      var p = this.rvalue(n.e);
      if (p.t.k !== 'ptr') cerr("cannot dereference '" + this.text(n.e) + "': it has type '" + typeStr(p.t) + "', not a pointer", n);
      var to = p.t.to;
      if (to.k === 'void') cerr("cannot dereference a 'void *' pointer (cast it to the right pointer type first)", n);
      var gp = p.get, txt = this.text(n.e);
      var addrF = function () { var a = gp(); if (a === 0) rt("dereferencing NULL pointer '" + txt + "'"); return a; };
      if (to.k === 'arr' || to.k === 'struct') return E(to, addrF, { addr: addrF, lv: true, node: n });
      if (to.k === 'struct' && !to.complete) cerr('dereferencing pointer to incomplete type', n);
      var ld = loader(to);
      return E(to, function () { return ld(addrF()); }, { addr: addrF, lv: true, node: n });
    }
    var e2 = this.rvalue(n.e);
    var g = e2.get;
    if (op === '!') {
      if (!isScalar(e2.t)) cerr("invalid operand to '!'", n);
      var r = E(T.int, function () { return g() ? 0 : 1; }, { node: n });
      if (e2.cnst !== undefined) r.cnst = e2.cnst ? 0 : 1;
      return r;
    }
    if (!isArith(e2.t)) cerr("invalid operand to unary '" + op + "' (type '" + typeStr(e2.t) + "')", n);
    var t = promote(e2.t);
    if (op === '+') return E(t, g, { node: n, cnst: e2.cnst });
    if (op === '-') {
      var cv = convFn(t, t);
      var res = E(t, t.k === 'float' ? function () { return -g(); } : t.size === 4 ? (t.signed ? function () { return (-g()) | 0; } : function () { return (-g()) >>> 0; }) : function () { return -g(); }, { node: n });
      if (e2.cnst !== undefined) res.cnst = t.k === 'float' ? -e2.cnst : t.size === 4 ? (t.signed ? (-e2.cnst) | 0 : (-e2.cnst) >>> 0) : -e2.cnst;
      return res;
    }
    if (op === '~') {
      if (t.k !== 'int') cerr("invalid operand to '~'", n);
      return E(t, t.size === 8 ? function () { return Number(~BigInt(g())); } : t.signed ? function () { return ~g(); } : function () { return (~g()) >>> 0; }, { node: n, cnst: e2.cnst !== undefined ? ~e2.cnst : undefined });
    }
    cerr('bad unary operator', n);
  };

  C.lvalueCheck = function (e, n, what) {
    if (e.t.k === 'arr') cerr("cannot " + what + " array '" + this.text(n) + "' (arrays cannot be assigned as a whole; copy element by element" + (e.t.of.k === 'int' && e.t.of.size === 1 ? ', or use strcpy for strings' : '') + ')', n);
    if (!e.lv || !e.addr) cerr("expression '" + this.text(n) + "' is not assignable", n);
  };

  C.incdec = function (n) {
    var e = this.expr(n.e);
    this.lvalueCheck(e, n.e, n.op === '++' ? 'increment' : 'decrement');
    var t = e.t;
    if (!isScalar(t)) cerr("cannot apply '" + n.op + "' to type '" + typeStr(t) + "'", n);
    var delta = n.op === '++' ? 1 : -1;
    if (t.k === 'ptr') { if (t.to.k === 'void') cerr('arithmetic on a void * pointer', n); delta *= t.to.size; }
    var af = e.addr, ld = loader(t), st = storer(t), cv = convFn(t.k === 'ptr' ? T.long : t, t);
    if (t.k === 'ptr') cv = function (v) { return v; };
    if (n.k === 'preinc') return E(t, function () { var a = af(); var v = cv(ld(a) + delta); st(a, v); return v; }, { node: n });
    return E(t, function () { var a = af(); var old = ld(a); st(a, cv(old + delta)); return old; }, { node: n });
  };

  // core binary arithmetic: returns {t, fn(a,b)} for given operand types (after decay)
  C.arith = function (op, lt, rt2, n, ltxt, rtxt) {
    var self = this;
    // pointer arithmetic
    if (op === '+' || op === '-') {
      if (lt.k === 'ptr' && rt2.k === 'int') {
        if (lt.to.k === 'void') cerr('arithmetic on a void * pointer', n);
        var sz = lt.to.size;
        return { t: lt, fn: op === '+' ? function (a, b) { return a + b * sz; } : function (a, b) { return a - b * sz; } };
      }
      if (op === '+' && lt.k === 'int' && rt2.k === 'ptr') { var sz2 = rt2.to.size; return { t: rt2, fn: function (a, b) { return b + a * sz2; } }; }
      if (op === '-' && lt.k === 'ptr' && rt2.k === 'ptr') {
        if (!sameType(lt.to, rt2.to)) cerr('subtracting pointers of different types', n);
        var sz3 = lt.to.size; return { t: T.long, fn: function (a, b) { return Math.trunc((a - b) / sz3); } };
      }
    }
    if (op === '==' || op === '!=' || op === '<' || op === '>' || op === '<=' || op === '>=') {
      if (lt.k === 'ptr' || rt2.k === 'ptr') {
        if (lt.k === 'float' || rt2.k === 'float' || lt.k === 'struct' || rt2.k === 'struct') cerr("invalid comparison between '" + typeStr(lt) + "' and '" + typeStr(rt2) + "'", n);
      } else if (!isArith(lt) || !isArith(rt2)) cerr("invalid operands to '" + op + "' ('" + typeStr(lt) + "' and '" + typeStr(rt2) + "')" + (lt.k === 'struct' || rt2.k === 'struct' ? ': structs cannot be compared with ' + op + ', compare their fields' : ''), n);
      var ct = (lt.k === 'ptr' || rt2.k === 'ptr') ? T.long : arithType(promote(lt), promote(rt2));
      var cl = convFn(lt.k === 'ptr' ? T.long : lt, ct), cr = convFn(rt2.k === 'ptr' ? T.long : rt2, ct);
      if (ct === T.ulong) { var cl0 = cl, cr0 = cr; cl = function (v) { v = cl0(v); return v < 0 ? v + 18446744073709551616 : v; }; cr = function (v) { v = cr0(v); return v < 0 ? v + 18446744073709551616 : v; }; }
      var f;
      switch (op) {
        case '==': f = function (a, b) { return cl(a) === cr(b) ? 1 : 0; }; break;
        case '!=': f = function (a, b) { return cl(a) !== cr(b) ? 1 : 0; }; break;
        case '<': f = function (a, b) { return cl(a) < cr(b) ? 1 : 0; }; break;
        case '>': f = function (a, b) { return cl(a) > cr(b) ? 1 : 0; }; break;
        case '<=': f = function (a, b) { return cl(a) <= cr(b) ? 1 : 0; }; break;
        case '>=': f = function (a, b) { return cl(a) >= cr(b) ? 1 : 0; }; break;
      }
      return { t: T.int, fn: f };
    }
    if (!isArith(lt) || !isArith(rt2)) {
      var hint = '';
      if (lt.k === 'ptr' || rt2.k === 'ptr') hint = ' (pointers only support + and - with integers)';
      if ((lt.k === 'arr' || rt2.k === 'arr')) hint = '';
      cerr("invalid operands to '" + op + "' ('" + typeStr(lt) + "' and '" + typeStr(rt2) + "')" + hint, n);
    }
    var rt3;
    if (op === '<<' || op === '>>') { rt3 = promote(lt); if (rt3.k !== 'int' || promote(rt2).k !== 'int') cerr("invalid operands to '" + op + "'", n); }
    else rt3 = arithType(promote(lt), promote(rt2));
    var c1 = convFn(lt, rt3), c2 = convFn(rt2, rt3);
    var flt = rt3.k === 'float', s4 = rt3.size === 4, sg = rt3.signed;
    var wrap = flt ? function (v) { return v; } : s4 ? (sg ? function (v) { return v | 0; } : function (v) { return v >>> 0; }) : function (v) { return v; };
    var divzero = "division by zero in '" + (ltxt || '') + ' ' + op + ' ' + (rtxt || '') + "'";
    var fn;
    switch (op) {
      case '+': fn = function (a, b) { return wrap(c1(a) + c2(b)); }; break;
      case '-': fn = function (a, b) { return wrap(c1(a) - c2(b)); }; break;
      case '*': fn = (!flt && s4) ? (sg ? function (a, b) { return Math.imul(c1(a), c2(b)); } : function (a, b) { return Math.imul(c1(a), c2(b)) >>> 0; }) : function (a, b) { return wrap(c1(a) * c2(b)); }; break;
      case '/': fn = flt ? function (a, b) { return c1(a) / c2(b); } : function (a, b) { var y = c2(b); if (y === 0) rt(divzero); return wrap(Math.trunc(c1(a) / y)); }; break;
      case '%': if (flt) cerr("invalid operands to '%' (use fmod for doubles)", n);
        fn = function (a, b) { var y = c2(b); if (y === 0) rt("remainder by zero in '" + (ltxt || '') + ' % ' + (rtxt || '') + "'"); return wrap(c1(a) % y); }; break;
      case '<<': fn = s4 ? (sg ? function (a, b) { return c1(a) << b; } : function (a, b) { return (c1(a) << b) >>> 0; }) : function (a, b) { return Number(BigInt.asIntN(64, BigInt(c1(a)) << BigInt(b))); }; break;
      case '>>': fn = s4 ? (sg ? function (a, b) { return c1(a) >> b; } : function (a, b) { return c1(a) >>> b; }) : function (a, b) { return Number(BigInt(Math.trunc(c1(a))) >> BigInt(b)); }; break;
      case '&': if (flt) cerr("invalid operands to '&'", n); fn = s4 ? (sg ? function (a, b) { return c1(a) & c2(b); } : function (a, b) { return (c1(a) & c2(b)) >>> 0; }) : function (a, b) { return Number(BigInt.asIntN(64, BigInt(c1(a)) & BigInt(c2(b)))); }; break;
      case '|': if (flt) cerr("invalid operands to '|'", n); fn = s4 ? (sg ? function (a, b) { return c1(a) | c2(b); } : function (a, b) { return (c1(a) | c2(b)) >>> 0; }) : function (a, b) { return Number(BigInt.asIntN(64, BigInt(c1(a)) | BigInt(c2(b)))); }; break;
      case '^': if (flt) cerr("invalid operands to '^' (note: ^ is XOR in C, use pow() from math.h for powers)", n); fn = s4 ? (sg ? function (a, b) { return c1(a) ^ c2(b); } : function (a, b) { return (c1(a) ^ c2(b)) >>> 0; }) : function (a, b) { return Number(BigInt.asIntN(64, BigInt(c1(a)) ^ BigInt(c2(b)))); }; break;
      default: cerr('unknown operator ' + op, n);
    }
    return { t: rt3, fn: fn };
  };

  C.binary = function (n) {
    var op = n.op;
    if (op === '&&' || op === '||') {
      var a = this.truthy(n.l), b = this.truthy(n.r);
      var r = E(T.int, op === '&&' ? function () { return a() && b() ? 1 : 0; } : function () { return a() || b() ? 1 : 0; }, { node: n });
      return r;
    }
    var l = this.rvalue(n.l), rr = this.rvalue(n.r);
    if ((op === '==' || op === '!=') && ((n.l.k === 'str') || (n.r.k === 'str'))) cerr("comparing strings with '" + op + "' compares addresses, not text: use strcmp(a, b) == 0", n);
    if ((op === '<' || op === '>' || op === '<=' || op === '>=') && n.l.k === 'binary' && /^(<|>|<=|>=)$/.test(n.l.op) && !n.l.parens) this.warn("'" + this.text(n) + "' does not mean what it does in maths: write it as two comparisons joined with &&", n);
    var ar = this.arith(op, l.t, rr.t, n, this.text(n.l), this.text(n.r));
    var f = ar.fn, gl = l.get, gr = rr.get;
    var res = E(ar.t, function () { return f(gl(), gr()); }, { node: n });
    if (l.cnst !== undefined && rr.cnst !== undefined && !(op === '/' || op === '%') ) { try { res.cnst = f(l.cnst, rr.cnst); } catch (e) { } }
    else if (l.cnst !== undefined && rr.cnst !== undefined && rr.cnst !== 0) { res.cnst = f(l.cnst, rr.cnst); }
    return res;
  };

  C.assign = function (n) {
    var self = this;
    var l = this.expr(n.l);
    this.lvalueCheck(l, n.l, 'assign to');
    var t = l.t, af = l.addr;
    if (n.op === '=') {
      var r = this.rvalue(n.r);
      if (r.t.k === 'void') cerr('cannot assign a void value (the function does not return anything)', n);
      this.checkAssign(t, r, n, 'assign to');
      if (t.k === 'struct') {
        var gr = r.get, sz = t.size;
        return E(t, function () { var src = gr(); var dst = af(); memcopy(dst, src, sz); return dst; }, { node: n });
      }
      var cv = convFn(r.t, t), st = storer(t), g = r.get;
      return E(t, function () { var v = cv(g()); st(af(), v); return v; }, { node: n });
    }
    var bop = n.op.slice(0, -1);
    var rv = this.rvalue(n.r);
    if (t.k === 'struct') cerr("invalid operands to '" + n.op + "'", n);
    var ar = this.arith(bop, t, rv.t, n, this.text(n.l), this.text(n.r));
    if (t.k === 'ptr' && ar.t.k !== 'ptr') cerr("invalid operands to '" + n.op + "'", n);
    var ld = loader(t), st2 = storer(t), cv2 = t.k === 'ptr' ? function (v) { return v; } : convFn(ar.t, t), f = ar.fn, gr2 = rv.get;
    return E(t, function () { var a = af(); var v = cv2(f(ld(a), gr2())); st2(a, v); return v; }, { node: n });
  };

  C.index = function (n) {
    var base = this.expr(n.a), idx = this.rvalue(n.i);
    var bt = base.t, it = idx.t;
    if (bt.k !== 'arr' && bt.k !== 'ptr') {
      var b2 = this.decay(base);
      if ((it.k === 'arr' || it.k === 'ptr') && isInt(b2.t)) cerr('write the array first: a[i], not i[a]', n);
      cerr("cannot index '" + this.text(n.a) + "' with [ ]: it has type '" + typeStr(bt) + "', not an array or pointer", n);
    }
    if (!isInt(it)) cerr("array index must be an integer, not '" + typeStr(it) + "'", n.i);
    var elem = bt.k === 'arr' ? bt.of : bt.to;
    if (elem.k === 'void') cerr('cannot index a void * pointer', n);
    if (elem.k === 'struct' && !elem.complete) cerr('indexing pointer to incomplete struct', n);
    var esz = elem.size;
    var gb = bt.k === 'arr' ? base.addr : base.get, gi = idx.get;
    var addrF;
    var txt = this.text(n.a);
    if (bt.k === 'arr' && bt.len != null) {
      var len = bt.len, tdesc = typeStr(bt);
      addrF = function () { var i = gi(); if (i < 0 || i >= len) rt('index ' + i + ' out of bounds for type \'' + tdesc + '\' (valid indexes for ' + txt + ' are 0 to ' + (len - 1) + ')'); return gb() + i * esz; };
    } else {
      addrF = function () { var p = gb(); if (p === 0) rt("indexing NULL pointer '" + txt + "'"); return p + gi() * esz; };
    }
    if (elem.k === 'arr' || elem.k === 'struct') return E(elem, addrF, { addr: addrF, lv: true, node: n });
    var ld = loader(elem);
    return E(elem, function () { return ld(addrF()); }, { addr: addrF, lv: true, node: n });
  };

  C.member = function (n) {
    var base, st, addrBase;
    var txt = this.text(n.e);
    if (n.arrow) {
      base = this.rvalue(n.e);
      if (base.t.k !== 'ptr') {
        if (base.t.k === 'struct') cerr("'" + txt + "' is a struct, not a pointer: use '" + txt + '.' + n.name + "' instead of '->'", n);
        cerr("'->' needs a pointer to a struct, but '" + txt + "' has type '" + typeStr(base.t) + "'", n);
      }
      st = base.t.to;
      if (st.k !== 'struct') cerr("'->' needs a pointer to a struct, but '" + txt + "' has type '" + typeStr(base.t) + "'", n);
      var gp = base.get, nm = n.name;
      addrBase = function () { var p = gp(); if (p === 0) rt("accessing field '" + nm + "' via a NULL pointer ('" + txt + "' is NULL)"); return p; };
    } else {
      base = this.expr(n.e);
      st = base.t;
      if (st.k === 'ptr' && st.to.k === 'struct') cerr("'" + txt + "' is a pointer: use '" + txt + '->' + n.name + "' instead of '.'", n);
      if (st.k !== 'struct') cerr("'.' needs a struct, but '" + txt + "' has type '" + typeStr(st) + "'", n);
      addrBase = base.addr || base.get;
    }
    if (!st.complete) cerr("incomplete type 'struct " + st.tag + "' (the struct is declared but its fields are not defined)", n);
    var f = null;
    for (var i = 0; i < st.fields.length; i++) if (st.fields[i].name === n.name) f = st.fields[i];
    if (!f) cerr("no member named '" + n.name + "' in 'struct " + (st.tag || '') + "'" + (st.fields.length ? ' (fields are: ' + st.fields.map(function (x) { return x.name; }).join(', ') + ')' : ''), n.tok);
    var off = f.offset, ft = f.type;
    var addrF = function () { return addrBase() + off; };
    if (ft.k === 'arr' || ft.k === 'struct') return E(ft, addrF, { addr: addrF, lv: base.lv !== false || n.arrow, node: n });
    var ld = loader(ft);
    return E(ft, function () { return ld(addrF()); }, { addr: addrF, lv: true, node: n });
  };

  // ---- function calls
  C.call = function (n) {
    var self = this;
    if (n.f.k !== 'id') cerr('only direct function calls like f(x) are supported', n);
    var name = n.f.name;
    var sym = this.lookup(name);
    if (sym && sym.kind !== 'func') cerr("'" + name + "' is a variable of type '" + typeStr(sym.type) + "', not a function", n);
    if (!sym) {
      var bi = BUILTINS[name];
      if (bi) {
        if (!this.includes[bi.h]) cerr("call to undeclared library function '" + name + "': add #include <" + bi.h + '> at the top of your file', n);
        return this.builtinCall(n, name, bi);
      }
      var near = this.nearName(name);
      cerr("call to undeclared function '" + name + "'" + (near ? " (did you mean '" + near + "'?)" : '') + ' - functions must be declared before they are used (add a prototype above main)', n);
    }
    var F = sym.F, ft = F.type;
    if (!ft.unspecified && !ft.variadic && n.args.length !== ft.params.length) cerr('too ' + (n.args.length > ft.params.length ? 'many' : 'few') + " arguments to function call '" + name + "': expected " + ft.params.length + ', have ' + n.args.length, n);
    var argFns = [], structSizes = [];
    n.args.forEach(function (an, i) {
      var e = self.rvalue(an);
      if (e.t.k === 'void') cerr('argument ' + (i + 1) + " to '" + name + "' has type void", an);
      var pt = ft.params[i];
      if (pt) {
        self.checkAssign(pt, e, an, 'pass argument ' + (i + 1) + ' of \'' + name + '\' as');
        var cv = convFn(e.t, pt), g = e.get;
        argFns.push(pt.k === 'struct' ? g : function () { return cv(g()); });
      } else argFns.push(e.get);
    });
    var nArgs = argFns.length;
    var ret = ft.ret;
    var get = function () {
      var vals = new Array(nArgs);
      for (var i = 0; i < nArgs; i++) vals[i] = argFns[i]();
      return callUser(F, vals);
    };
    return E(ret, get, { node: n, addr: ret.k === 'struct' ? get : null, lv: false });
  };

  // ---- function definition compile
  C.compileFunction = function (fnNode) {
    var name = fnNode.name, ft = fnNode.type;
    var F = this.declareFunc(name, ft, fnNode);
    if (F.defined) cerr("redefinition of function '" + name + "'", fnNode);
    F.defined = true;
    F.line = fnNode.line;
    this.fn = { F: F, frameSize: 0, locals: [] };
    this.scope = { vars: {}, parent: null };
    var self = this;
    F.params = [];
    ft.params.forEach(function (pt, i) {
      var pn = fnNode.paramNames[i];
      if (Object.prototype.hasOwnProperty.call(self.scope.vars, pn)) cerr("duplicate parameter '" + pn + "'", fnNode.paramToks[i]);
      var sym = self.allocLocal(pn, pt, fnNode.paramToks[i], 'parameter');
      F.params.push({ off: sym.off, type: pt, st: pt.k === 'struct' ? null : storer(pt) });
    });
    if (name === 'main') {
      if (ft.ret.k !== 'int' && ft.ret.k !== 'void') cerr("'main' must return 'int'", fnNode);
    }
    this.retType = ft.ret;
    var body = this.block(fnNode.body, false);
    F.body = body;
    F.frameSize = this.fn.frameSize;
    F.locals = this.fn.locals;
    this.fn = null; this.scope = null;
  };
  C.declareFunc = function (name, ft, node) {
    if (Object.prototype.hasOwnProperty.call(this.globals, name)) cerr("'" + name + "' redeclared as a different kind of symbol", node);
    var F = this.funcs[name];
    if (F) {
      var a = F.type, b = ft;
      var ok = sameType(a.ret, b.ret) && (a.unspecified || b.unspecified || (a.params.length === b.params.length && a.params.every(function (p, i) { return sameType(p, b.params[i]); })));
      if (!ok) cerr("conflicting types for '" + name + "': the prototype says '" + typeStr(a) + "' but here it is '" + typeStr(b) + "'", node);
      if (a.unspecified && !b.unspecified) F.type = b;
      return F;
    }
    F = { name: name, type: ft, defined: false, line: node.line };
    this.funcs[name] = F;
    return F;
  };
  C.allocLocal = function (name, type, tok, kind) {
    if (type.k === 'void') cerr("variable '" + name + "' declared void", tok);
    if (type.k === 'struct' && !type.complete) cerr("variable '" + name + "' has incomplete type 'struct " + type.tag + "'", tok);
    if (type.k === 'arr' && type.len == null) cerr("array '" + name + "' needs a size or an initializer", tok);
    if (Object.prototype.hasOwnProperty.call(this.scope.vars, name)) cerr("redefinition of '" + name + "'", tok);
    var off = alignUp(this.fn.frameSize, Math.max(8, type.align));
    this.fn.frameSize = off + type.size + 16;
    var desc = (kind || 'variable') + " '" + name + "'";
    this.fn.locals.push({ off: off, size: type.size, desc: desc, type: type });
    var sym = { kind: 'var', type: type, off: off, local: true };
    this.scope.vars[name] = sym;
    return sym;
  };

  // ---- statements
  C.block = function (node, newScope) {
    var self = this;
    if (newScope !== false) this.scope = { vars: {}, parent: this.scope };
    var fns = [];
    node.items.forEach(function (it) { var f = self.stmt(it); if (f) fns.push(f); });
    if (newScope !== false) this.scope = this.scope.parent;
    var len = fns.length;
    if (len === 1) return fns[0];
    return function () { for (var i = 0; i < len; i++) { var r = fns[i](); if (r) return r; } return 0; };
  };

  C.stmt = function (n) {
    var self = this, line = n.line;
    switch (n.k) {
      case 'block': return this.block(n, true);
      case 'empty': return null;
      case 'expr': {
        var e = this.expr(n.e);
        if (e.t.k === 'func') cerr("function '" + (e.fname || '') + "' used without calling it (add parentheses)", n);
        if (n.e.k === 'binary' && n.e.op === '==' ) this.warn("result of '==' comparison is unused: did you mean '=' (assignment)?", n.e);
        var g = e.get;
        return function () { LINE = line; g(); return 0; };
      }
      case 'decl': return this.localDecl(n);
      case 'if': {
        var c = this.truthy(n.c);
        var t = this.stmtOrNop(n.t), f = n.f ? this.stmtOrNop(n.f) : null;
        if (f) return function () { LINE = line; return c() ? t() : f(); };
        return function () { LINE = line; return c() ? t() : 0; };
      }
      case 'while': {
        var cw = this.truthy(n.c);
        this.loopDepth++; var bw = this.stmtOrNop(n.body); this.loopDepth--;
        return function () {
          while (true) {
            LINE = line;
            if (!cw()) break;
            if (++STEPS > STEP_LIMIT) tle();
            var r = bw();
            if (r === BRK) break;
            if (r === RET) return r;
          }
          return 0;
        };
      }
      case 'do': {
        this.loopDepth++; var bd = this.stmtOrNop(n.body); this.loopDepth--;
        var cd = this.truthy(n.c);
        return function () {
          while (true) {
            if (++STEPS > STEP_LIMIT) tle();
            var r = bd();
            if (r === BRK) break;
            if (r === RET) return r;
            LINE = line;
            if (!cd()) break;
          }
          return 0;
        };
      }
      case 'for': {
        this.scope = { vars: {}, parent: this.scope };
        var init = n.init ? this.stmt(n.init) : null;
        var cf = n.c ? this.truthy(n.c) : function () { return 1; };
        var se = n.step ? this.expr(n.step) : null;
        var step = se ? se.get : null;
        this.loopDepth++; var bf = this.stmtOrNop(n.body); this.loopDepth--;
        this.scope = this.scope.parent;
        return function () {
          LINE = line;
          if (init) init();
          while (true) {
            LINE = line;
            if (!cf()) break;
            if (++STEPS > STEP_LIMIT) tle();
            var r = bf();
            if (r === BRK) break;
            if (r === RET) return r;
            LINE = line;
            if (step) step();
          }
          return 0;
        };
      }
      case 'return': {
        var rt0 = this.retType;
        if (!n.e) {
          if (rt0.k !== 'void' && this.fn.F.name !== 'main') cerr('non-void function should return a value', n);
          return function () { LINE = line; RETV = 0; return RET; };
        }
        var re = this.rvalue(n.e);
        if (rt0.k === 'void') { if (re.t.k !== 'void') cerr("void function '" + this.fn.F.name + "' should not return a value", n); var gv = re.get; return function () { LINE = line; gv(); RETV = 0; return RET; }; }
        this.checkAssign(rt0, re, n, 'return');
        var gr = re.get;
        if (rt0.k === 'struct') {
          var sz = rt0.size;
          return function () {
            LINE = line; var src = gr();
            var tmp = allocTemp(sz); memcopy(tmp, src, sz); RETV = tmp; return RET;
          };
        }
        var cv = convFn(re.t, rt0);
        return function () { LINE = line; RETV = cv(gr()); return RET; };
      }
      case 'break':
        if (!this.loopDepth && !this.switchDepth) cerr("'break' statement not in a loop or switch", n);
        return function () { return BRK; };
      case 'continue':
        if (!this.loopDepth) cerr("'continue' statement not in a loop", n);
        return function () { return CONT; };
      case 'switch': return this.switchStmt(n);
      case 'case': case 'default': cerr("'" + n.k + "' label must be directly inside a switch block", n);
    }
    cerr('unsupported statement', n);
  };
  C.stmtOrNop = function (n) { var f = this.stmt(n); return f || function () { return 0; }; };

  C.switchStmt = function (n) {
    var self = this, line = n.line;
    var e = this.rvalue(n.e);
    if (!isInt(e.t)) cerr('switch value must be an integer (or char)', n.e);
    if (n.body.k !== 'block') cerr('switch body must be a { } block', n.body);
    this.scope = { vars: {}, parent: this.scope };
    this.switchDepth++;
    var fns = [], cases = new Map(), def = -1;
    n.body.items.forEach(function (it) {
      if (it.k === 'case') {
        var ce = self.expr(it.e);
        if (ce.cnst === undefined) cerr('case value must be a constant', it);
        if (cases.has(ce.cnst)) cerr('duplicate case value ' + ce.cnst, it);
        cases.set(ce.cnst, fns.length);
        return;
      }
      if (it.k === 'default') { if (def >= 0) cerr('multiple default labels', it); def = fns.length; return; }
      var f = self.stmt(it); if (f) fns.push(f);
    });
    this.switchDepth--;
    this.scope = this.scope.parent;
    var g = e.get, len = fns.length;
    return function () {
      LINE = line;
      var v = g();
      var start = cases.has(v) ? cases.get(v) : def;
      if (start < 0) return 0;
      for (var i = start; i < len; i++) { var r = fns[i](); if (r === BRK) return 0; if (r) return r; }
      return 0;
    };
  };

  C.localDecl = function (n) {
    var self = this, fns = [];
    n.decls.forEach(function (d) {
      var t = d.type;
      if (t.k === 'func') { self.declareFunc(d.name, t, d.tok); return; }
      if (t.k === 'arr' && t.len == null && d.init) t = self.inferArrayLen(t, d.init, d.tok);
      if (d.isStatic) {
        if (Object.prototype.hasOwnProperty.call(self.scope.vars, d.name)) cerr("redefinition of '" + d.name + "'", d.tok);
        var ga = allocGlobal(t.size, t.align, "static variable '" + d.name + "'", false, t);
        setInit(ga, t.size);
        self.scope.vars[d.name] = { kind: 'var', type: t, global: true, addr: ga };
        if (d.init) { var initF = self.initializer(t, d.init, d.tok, true); self.staticInits.push(function () { initF(ga); }); }
        return;
      }
      // compile initializer BEFORE declaring the name (int x = x; is an error anyway)
      var initFn = d.init ? self.initializer(t, d.init, d.tok, false) : null;
      var sym = self.allocLocal(d.name, t, d.tok);
      var off = sym.off, line = d.tok.line, size = t.size;
      if (initFn) fns.push(function () { LINE = line; initFn(FP + off); return 0; });
    });
    if (!fns.length) return null;
    if (fns.length === 1) return fns[0];
    return function () { for (var i = 0; i < fns.length; i++) fns[i](); return 0; };
  };

  C.inferArrayLen = function (t, init, tok) {
    if (init.k === 'str') { if (!(t.of.k === 'int' && t.of.size === 1)) cerr('string initializer for a non-char array', tok); return arrT(t.of, init.bytes.length + 1); }
    if (init.k !== 'initlist') cerr("array needs a { } initializer", tok);
    var max = 0, cur = 0;
    var self = this;
    init.items.forEach(function (it) {
      if (it.desig.length && it.desig[0].index !== undefined) cur = it.desig[0].index;
      cur++;
      // brace elision: count scalars per element
      if (!it.desig.length && it.v.k !== 'initlist' && t.of.k !== 'int' && t.of.k !== 'float' && t.of.k !== 'ptr') {
        // flat initializer for aggregate elements
      }
      max = Math.max(max, cur);
    });
    if (t.of.k === 'arr' || t.of.k === 'struct') {
      var flat = init.items.every(function (it) { return it.v.k !== 'initlist' && !it.desig.length; });
      if (flat && init.items.length) { var per = scalarCount(t.of); max = Math.ceil(init.items.length / per); }
    }
    if (max === 0) cerr('zero-size array', tok);
    return arrT(t.of, max);
  };
  function scalarCount(t) { if (t.k === 'arr') return t.len * scalarCount(t.of); if (t.k === 'struct') return t.fields.reduce(function (s, f) { return s + scalarCount(f.type); }, 0); return 1; }

  // returns function(addr) that initialises object at addr
  C.initializer = function (t, init, tok, isConst) {
    var self = this;
    if (init.k !== 'initlist') {
      if (t.k === 'arr') {
        if (init.k === 'str' && t.of.k === 'int' && t.of.size === 1) {
          var bytes = init.bytes, len = t.len;
          if (bytes.length > len) cerr('initializer string is too long for array of size ' + len + ' (needs ' + (bytes.length + 1) + ' including \'\\0\')', tok);
          return function (a) {
            for (var i = 0; i < len; i++) { U8[a + i] = i < bytes.length ? bytes[i] : 0; IB[a + i] = 1; }
          };
        }
        cerr("array must be initialised with a { } list" + (init.k === 'str' ? '' : ''), tok);
      }
      var e = this.rvalue(init);
      this.checkAssign(t, e, init, 'initialise');
      if (t.k === 'struct') { var gs = e.get, sz = t.size; return function (a) { memcopy(a, gs(), sz); }; }
      var cv = convFn(e.t, t), st = storer(t), g = e.get;
      return function (a) { st(a, cv(g())); };
    }
    // brace list: zero whole object then fill
    if (t.k !== 'arr' && t.k !== 'struct') {
      if (init.items.length === 0) cerr('empty initializer for scalar', tok);
      if (init.items.length > 1) cerr('too many values in initializer for a single variable', tok);
      return this.initializer(t, init.items[0].v, tok, isConst);
    }
    var ops = [];  // {off, fn(addr)}
    this.fillAggregate(t, 0, init.items, { i: 0 }, ops, tok, true);
    var size = t.size;
    return function (a) {
      chk(a, size, 1);
      U8.fill(0, a, a + size); IB.fill(1, a, a + size);
      for (var k = 0; k < ops.length; k++) ops[k].fn(a + ops[k].off);
    };
  };
  // consume items from list starting at cursor.i to fill aggregate t at base offset
  C.fillAggregate = function (t, base, items, cur, ops, tok, braced) {
    var self = this;
    if (t.k === 'arr') {
      var idx = 0;
      while (cur.i < items.length) {
        var it = items[cur.i];
        if (it.desig.length) {
          if (!braced) return;
          if (it.desig[0].index === undefined) cerr('field designator used in an array initializer', tok);
          idx = it.desig[0].index;
          if (t.len != null && idx >= t.len) cerr('array index ' + idx + ' in initializer exceeds array bounds', tok);
          var rest = it.desig.slice(1);
          if (rest.length) { cerr('nested designators are not supported', tok); }
          it = { desig: [], v: it.v };
          items = items.slice(); items[cur.i] = it;
        }
        if (t.len != null && idx >= t.len) { if (braced) cerr('too many values in array initializer (array has ' + t.len + ' elements)', tok); return; }
        this.fillOne(t.of, base + idx * t.of.size, items, cur, ops, tok);
        idx++;
      }
      return;
    }
    // struct
    var fi = 0;
    while (cur.i < items.length) {
      var it2 = items[cur.i];
      if (it2.desig.length) {
        if (!braced) return;
        var dname = it2.desig[0].field;
        if (dname === undefined) cerr('array designator used in a struct initializer', tok);
        fi = -1;
        for (var k = 0; k < t.fields.length; k++) if (t.fields[k].name === dname) fi = k;
        if (fi < 0) cerr("no field named '" + dname + "' in 'struct " + (t.tag || '') + "'", it2.desig[0].tok);
        items = items.slice(); items[cur.i] = { desig: [], v: it2.v };
      }
      if (fi >= t.fields.length) { if (braced) cerr('too many values in struct initializer', tok); return; }
      var f = t.fields[fi];
      this.fillOne(f.type, base + f.offset, items, cur, ops, tok);
      fi++;
    }
  };
  C.fillOne = function (t, off, items, cur, ops, tok) {
    var it = items[cur.i];
    if (t.k === 'arr' || t.k === 'struct') {
      if (it.v.k === 'initlist') {
        cur.i++;
        this.fillAggregate(t, off, it.v.items, { i: 0 }, ops, tok, true);
        return;
      }
      if (t.k === 'arr' && it.v.k === 'str' && t.of.k === 'int' && t.of.size === 1) {
        cur.i++;
        var f0 = this.initializer(t, it.v, tok, false);
        ops.push({ off: off, fn: f0 }); return;
      }
      if (t.k === 'struct') {
        var e0 = this.rvalue(it.v);
        if (e0.t === t) { cur.i++; var gg = e0.get, sz = t.size; ops.push({ off: off, fn: function (a) { memcopy(a, gg(), sz); } }); return; }
      }
      // brace elision
      this.fillAggregate(t, off, items, cur, ops, tok, false);
      return;
    }
    cur.i++;
    if (it.v.k === 'initlist') {
      if (it.v.items.length !== 1) cerr('too many braces around scalar initializer', tok);
      ops.push({ off: off, fn: this.initializer(t, it.v.items[0].v, tok, false) });
      return;
    }
    ops.push({ off: off, fn: this.initializer(t, it.v, tok, false) });
  };

  // ---- globals
  C.globalDecl = function (n) {
    var self = this;
    n.decls.forEach(function (d) {
      var t = d.type;
      if (t.k === 'func') { self.declareFunc(d.name, t, d.tok); return; }
      if (t.k === 'arr' && t.len == null && d.init) t = self.inferArrayLen(t, d.init, d.tok);
      if (t.k === 'arr' && t.len == null) cerr("array '" + d.name + "' needs a size", d.tok);
      if (t.k === 'struct' && !t.complete) cerr("variable '" + d.name + "' has incomplete type", d.tok);
      if (t.k === 'void') cerr("variable '" + d.name + "' declared void", d.tok);
      if (Object.prototype.hasOwnProperty.call(self.funcs, d.name)) cerr("'" + d.name + "' redeclared as a different kind of symbol", d.tok);
      var existing = self.globals[d.name];
      if (existing) { if (!sameType(existing.type, t)) cerr("conflicting types for '" + d.name + "'", d.tok); if (!d.init) return; }
      var a = existing ? existing.addr : allocGlobal(t.size, t.align, "global variable '" + d.name + "'", false, t);
      setInit(a, t.size);
      self.globals[d.name] = { kind: 'var', type: t, global: true, addr: a };
      if (d.init) { var f = self.initializer(t, d.init, d.tok, true); var line = d.tok.line; self.globalInits.push(function () { LINE = line; f(a); }); }
    });
  };

  // ------------------------------------------------------------------ runtime calls
  var STACK_DEPTH_LIMIT = 3000;
  function tle() { throw new CError('tle', 'Time limit exceeded: your program ran too long (infinite loop?)', LINE, 0); }
  function allocTemp(size) {
    var start = alignUp(hTop, 8);
    if (start + size + 16 > MEM) rt('out of memory');
    newRegion(start, size, 'temp', 'a temporary value', LINE);
    hTop = start + size + 16;
    return start;
  }
  var CUR_SP = STACK_BASE;
  function callUser(F, vals) {
    if (!F.defined) rt("function '" + F.name + "' was declared but never defined (no body)");
    if (++CALL_DEPTH > STACK_DEPTH_LIMIT) rt('stack overflow: too many nested function calls (infinite recursion? check your base case)');
    if (++STEPS > STEP_LIMIT) tle();
    var savedFP = FP, savedSP = CUR_SP, savedLine = LINE;
    var fp = alignUp(CUR_SP, 16);
    if (fp + F.frameSize > STACK_END) rt('stack overflow: local variables too large or recursion too deep');
    var locals = F.locals, ids = new Array(locals.length);
    for (var i = 0; i < locals.length; i++) {
      var L = locals[i], s = fp + L.off;
      ids[i] = newRegion(s, L.size, 'stack', L.desc, F.line, L.type);
      IB.fill(0, s, s + L.size);
    }
    FP = fp; CUR_SP = fp + F.frameSize;
    var params = F.params;
    for (var j = 0; j < params.length; j++) {
      var pa = fp + params[j].off;
      if (params[j].st) params[j].st(pa, vals[j]);
      else memcopy(pa, vals[j], params[j].type.size);
    }
    RETV = 0;
    var r = F.body();
    var result = RETV;
    if (r !== RET && F.type.ret.k !== 'void' && F.name !== 'main') {
      rt("function '" + F.name + "' reached the end without returning a value (every path in a non-void function needs a return)");
    }
    for (var k = 0; k < ids.length; k++) { killRegion(ids[k], 0); freeStackIds.push(ids[k]); }
    FP = savedFP; CUR_SP = savedSP; LINE = savedLine; CALL_DEPTH--;
    return result;
  }

  // ------------------------------------------------------------------ printf / scanf
  function exactFixed(x, prec) {
    // exact round-half-even formatting of a double, like glibc
    if (!isFinite(x)) return null;
    var neg = x < 0 || (x === 0 && 1 / x < 0);
    var ax = Math.abs(x);
    var s = ax.toFixed(Math.min(prec, 100));
    // check for an exact tie using BigInt rational arithmetic
    var bufd = new DataView(new ArrayBuffer(8)); bufd.setFloat64(0, ax);
    var hi = bufd.getUint32(0), lo = bufd.getUint32(4);
    var exp = (hi >>> 20) & 0x7ff;
    var mant = (BigInt(hi & 0xfffff) << 32n) | BigInt(lo);
    if (exp === 0) exp = 1; else mant |= (1n << 52n);
    var e2 = exp - 1075;
    if (e2 < 0) {
      var num = mant * (10n ** BigInt(prec)), den = 1n << BigInt(-e2);
      var q = num / den, r = num % den;
      if (r * 2n === den && q % 2n === 0n) {
        // tie, round down to even: q
        var qs = q.toString();
        while (qs.length <= prec) qs = '0' + qs;
        s = prec > 0 ? qs.slice(0, qs.length - prec) + '.' + qs.slice(qs.length - prec) : qs;
      }
    }
    return (neg ? '-' : '') + s;
  }
  function fmtExp(x, prec, upper) {
    if (!isFinite(x)) return null;
    var s = x.toExponential(Math.min(prec, 100));
    var m = /^(-?[\d.]+)e([+-])(\d+)$/.exec(s);
    var ex = m[3].length < 2 ? '0' + m[3] : m[3];
    var out = m[1] + 'e' + m[2] + ex;
    return upper ? out.toUpperCase() : out;
  }
  function fmtG(x, prec, upper, alt) {
    if (!isFinite(x)) return null;
    var P2 = prec === 0 ? 1 : prec;
    if (x === 0) { var z = alt ? (0).toFixed(P2 - 1) : '0'; return (1 / x < 0 ? '-' : '') + z; }
    var X = parseInt(x.toExponential(P2 - 1).split('e')[1], 10);
    var s;
    if (P2 > X && X >= -4) s = exactFixed(x, P2 - 1 - X);
    else s = fmtExp(x, P2 - 1, upper);
    if (!alt) {
      if (s.indexOf('e') >= 0 || s.indexOf('E') >= 0) { var parts = s.split(/(?=[eE])/); if (parts[0].indexOf('.') >= 0) parts[0] = parts[0].replace(/\.?0+$/, ''); s = parts.join(''); }
      else if (s.indexOf('.') >= 0) s = s.replace(/\.?0+$/, '');
    }
    return s;
  }
  function specials(x, upper) { var s = x !== x ? 'nan' : (x < 0 ? '-inf' : 'inf'); return upper ? s.toUpperCase() : s; }

  // format with args: array of {v, t}
  function cformat(fmtBytes, args, fname) {
    var out = [], ai = 0;
    function nextArg(conv) {
      if (ai >= args.length) rt(fname + ": not enough arguments for the % conversions in the format string (missing value for %" + conv + ')');
      return args[ai++];
    }
    for (var i = 0; i < fmtBytes.length; i++) {
      var c = fmtBytes[i];
      if (c !== 37) { out.push(c); continue; }
      i++;
      var flags = '';
      while (i < fmtBytes.length && '-+ #0'.indexOf(String.fromCharCode(fmtBytes[i])) >= 0) flags += String.fromCharCode(fmtBytes[i++]);
      var width = null;
      if (fmtBytes[i] === 42) { width = nextArg('*').v; i++; if (width < 0) { flags += '-'; width = -width; } }
      else { var w = ''; while (fmtBytes[i] >= 48 && fmtBytes[i] <= 57) w += String.fromCharCode(fmtBytes[i++]); if (w) width = parseInt(w, 10); }
      var prec = null;
      if (fmtBytes[i] === 46) {
        i++;
        if (fmtBytes[i] === 42) { prec = nextArg('*').v; i++; if (prec < 0) prec = null; }
        else { var p = ''; while (fmtBytes[i] >= 48 && fmtBytes[i] <= 57) p += String.fromCharCode(fmtBytes[i++]); prec = p ? parseInt(p, 10) : 0; }
      }
      var len = '';
      while (i < fmtBytes.length && 'hlLqjzt'.indexOf(String.fromCharCode(fmtBytes[i])) >= 0) len += String.fromCharCode(fmtBytes[i++]);
      var conv = String.fromCharCode(fmtBytes[i]);
      if (i >= fmtBytes.length) { out.push(37); break; }
      var s = null, isNum = true, sign = '';
      switch (conv) {
        case '%': out.push(37); continue;
        case 'd': case 'i': {
          var v = nextArg(conv).v; v = Math.trunc(v);
          if (len === '' || len === 'h' || len === 'hh') v = len === 'hh' ? (v << 24) >> 24 : len === 'h' ? (v << 16) >> 16 : v | 0;
          if (v < 0) { sign = '-'; v = -v; } else if (flags.indexOf('+') >= 0) sign = '+'; else if (flags.indexOf(' ') >= 0) sign = ' ';
          s = String(v);
          if (prec !== null) { while (s.length < prec) s = '0' + s; if (prec === 0 && v === 0) s = ''; }
          break;
        }
        case 'u': case 'x': case 'X': case 'o': {
          var uv = Math.trunc(nextArg(conv).v);
          var base = conv === 'u' ? 10 : conv === 'o' ? 8 : 16;
          if (len === '' || len === 'h' || len === 'hh') s = (uv >>> 0).toString(base);
          else s = uv < 0 ? BigInt.asUintN(64, BigInt(uv)).toString(base) : uv.toString(base);
          if (conv === 'X') s = s.toUpperCase();
          if (prec !== null) while (s.length < prec) s = '0' + s;
          if (flags.indexOf('#') >= 0 && uv !== 0) { if (conv === 'x') sign = '0x'; if (conv === 'X') sign = '0X'; if (conv === 'o') s = '0' + s; }
          break;
        }
        case 'c': { isNum = false; var cv = nextArg(conv).v & 255; s = null; var chars = [cv]; pad(chars); continue; }
        case 's': {
          isNum = false;
          var sa = nextArg(conv);
          if (sa.v === 0) rt(fname + ': %s was given a NULL pointer');
          var sb = readCStr(sa.v, fname + ' %s');
          if (prec !== null) sb = sb.slice(0, prec);
          pad(sb); continue;
        }
        case 'p': {
          var pv = nextArg(conv).v;
          s = pv === 0 ? '(nil)' : '0x' + Math.trunc(pv).toString(16); isNum = false;
          break;
        }
        case 'f': case 'F': case 'e': case 'E': case 'g': case 'G': {
          var fv = nextArg(conv).v;
          var pr = prec === null ? 6 : prec;
          var neg = fv < 0 || (fv === 0 && 1 / fv < 0);
          if (!isFinite(fv)) s = specials(Math.abs(fv), conv === 'F' || conv === 'E' || conv === 'G');
          else if (conv === 'f' || conv === 'F') s = exactFixed(Math.abs(fv), pr);
          else if (conv === 'e' || conv === 'E') s = fmtExp(Math.abs(fv), pr, conv === 'E');
          else s = fmtG(Math.abs(fv), pr, conv === 'G', flags.indexOf('#') >= 0);
          if (neg && !(fv !== fv)) sign = '-'; else if (flags.indexOf('+') >= 0) sign = '+'; else if (flags.indexOf(' ') >= 0) sign = ' ';
          if (s.charAt(0) === '-') s = s.slice(1);
          if (flags.indexOf('#') >= 0 && s.indexOf('.') < 0 && (conv === 'f' || conv === 'F')) s += '.';
          break;
        }
        default:
          rt(fname + ": unknown conversion '%" + conv + "' in format string");
      }
      // numeric padding
      var body = s, total = sign.length + body.length;
      var str;
      if (width !== null && total < width) {
        if (flags.indexOf('-') >= 0) str = sign + body + ' '.repeat(width - total);
        else if (flags.indexOf('0') >= 0 && isNum && (prec === null || 'fFeEgG'.indexOf(conv) >= 0)) str = sign + '0'.repeat(width - total) + body;
        else str = ' '.repeat(width - total) + sign + body;
      } else str = sign + body;
      for (var q = 0; q < str.length; q++) out.push(str.charCodeAt(q));
    }
    function pad(bytesArr) {
      var n = bytesArr.length;
      if (width !== null && n < width) {
        if (flags.indexOf('-') >= 0) { bytesArr.forEach(function (b) { out.push(b); }); for (var z = n; z < width; z++) out.push(32); }
        else { for (var z2 = n; z2 < width; z2++) out.push(32); bytesArr.forEach(function (b) { out.push(b); }); }
      } else bytesArr.forEach(function (b) { out.push(b); });
    }
    return out;
  }

  function emit(bytes, toErr) {
    var target = toErr ? ERR : OUT;
    for (var i = 0; i < bytes.length; i++) target.push(bytes[i]);
    if (OUT.length > OUT_LIMIT) { OUT.length = OUT_LIMIT; throw new CError('runtime', 'Output limit exceeded: your program printed too much (infinite loop with printf?)', LINE, 0); }
  }

  function isSpace(c) { return c === 32 || c === 9 || c === 10 || c === 13 || c === 11 || c === 12; }
  function cscanf(fmtBytes, ptrs, src) {
    // src: {peek(), get(), eof()}
    var assigned = 0, pi = 0, anyInput = false;
    for (var i = 0; i < fmtBytes.length; i++) {
      var c = fmtBytes[i];
      if (isSpace(c)) { while (!src.eof() && isSpace(src.peek())) src.get(); continue; }
      if (c !== 37) {
        if (src.eof()) return assigned === 0 && !anyInput ? -1 : assigned;
        if (src.peek() !== c) return assigned;
        src.get(); continue;
      }
      i++;
      var suppress = false;
      if (fmtBytes[i] === 42) { suppress = true; i++; }
      var w = ''; while (fmtBytes[i] >= 48 && fmtBytes[i] <= 57) w += String.fromCharCode(fmtBytes[i++]);
      var width = w ? parseInt(w, 10) : Infinity;
      var len = ''; while ('hlLqjzt'.indexOf(String.fromCharCode(fmtBytes[i])) >= 0) len += String.fromCharCode(fmtBytes[i++]);
      var conv = String.fromCharCode(fmtBytes[i]);
      if (conv === '%') { while (!src.eof() && isSpace(src.peek())) src.get(); if (src.eof()) return assigned || -1; if (src.peek() !== 37) return assigned; src.get(); continue; }
      if (conv !== 'c' && conv !== '[') { while (!src.eof() && isSpace(src.peek())) src.get(); }
      if (src.eof()) return assigned === 0 ? -1 : assigned;
      anyInput = true;
      var target = suppress ? null : ptrs[pi++];
      if (!suppress && !target) rt('scanf: more % conversions than variables to store into');
      if (conv === 'd' || conv === 'i' || conv === 'u' || conv === 'x' || conv === 'o') {
        var txt = '', cnt = 0;
        if ((src.peek() === 45 || src.peek() === 43) && cnt < width) { txt += String.fromCharCode(src.get()); cnt++; }
        var hex = conv === 'x';
        while (!src.eof() && cnt < width && (hex ? /[0-9a-fA-F]/.test(String.fromCharCode(src.peek())) : (src.peek() >= 48 && src.peek() <= 57))) { txt += String.fromCharCode(src.get()); cnt++; }
        if (!/[0-9a-fA-F]/.test(txt)) return assigned;
        var val = parseInt(txt, hex ? 16 : conv === 'o' ? 8 : 10);
        if (target) { target.store(val); assigned++; }
      } else if (conv === 'f' || conv === 'e' || conv === 'g' || conv === 'E' || conv === 'G') {
        var ft = '', fc = 0;
        var m2 = function (re) { return !src.eof() && fc < width && re.test(String.fromCharCode(src.peek())); };
        if (m2(/[+-]/)) { ft += String.fromCharCode(src.get()); fc++; }
        while (m2(/[0-9]/)) { ft += String.fromCharCode(src.get()); fc++; }
        if (m2(/\./)) { ft += String.fromCharCode(src.get()); fc++; while (m2(/[0-9]/)) { ft += String.fromCharCode(src.get()); fc++; } }
        if (/[0-9]/.test(ft) && m2(/[eE]/)) {
          ft += String.fromCharCode(src.get()); fc++;
          if (m2(/[+-]/)) { ft += String.fromCharCode(src.get()); fc++; }
          while (m2(/[0-9]/)) { ft += String.fromCharCode(src.get()); fc++; }
        }
        if (!/[0-9]/.test(ft)) return assigned;
        if (target) { target.store(parseFloat(ft)); assigned++; }
      } else if (conv === 'c') {
        var n = width === Infinity ? 1 : width, chars = [];
        for (var k = 0; k < n; k++) { if (src.eof()) break; chars.push(src.get()); }
        if (!chars.length) return assigned || -1;
        if (target) { target.storeBytes(chars, false); assigned++; }
      } else if (conv === 's') {
        var sb = [];
        while (!src.eof() && !isSpace(src.peek()) && sb.length < width) sb.push(src.get());
        if (target) { target.storeBytes(sb, true); assigned++; }
      } else if (conv === '[') {
        i++;
        var neg = false; if (fmtBytes[i] === 94) { neg = true; i++; }
        var set = [];
        if (fmtBytes[i] === 93) { set.push(93); i++; }
        while (i < fmtBytes.length && fmtBytes[i] !== 93) set.push(fmtBytes[i++]);
        var inSet = function (ch) { var f = false; for (var q = 0; q < set.length; q++) { if (set[q + 1] === 45 && set[q + 2] !== undefined) { if (ch >= set[q] && ch <= set[q + 2]) f = true; q += 2; } else if (set[q] === ch) f = true; } return neg ? !f : f; };
        var sb2 = [];
        while (!src.eof() && inSet(src.peek()) && sb2.length < width) sb2.push(src.get());
        if (!sb2.length) return assigned;
        if (target) { target.storeBytes(sb2, true); assigned++; }
      } else rt("scanf: unsupported conversion '%" + conv + "'");
    }
    return assigned;
  }
  var STDIN_SRC = {
    peek: function () { return INPUT[INPOS]; },
    get: function () { return INPUT[INPOS++]; },
    eof: function () { return INPOS >= INPUT.length; }
  };
  function strSrc(bytes) { var p = 0; return { peek: function () { return bytes[p]; }, get: function () { return bytes[p++]; }, eof: function () { return p >= bytes.length; } }; }

  // ------------------------------------------------------------------ builtins
  // h: header, sig: [ret, params...] as type names; impl(args) where args = [{v,t}]
  var B = {};
  function def(h, name, ret, params, impl, variadic) { B[name] = { h: h, ret: ret, params: params, impl: impl, variadic: !!variadic }; }
  var BUILTINS = B;
  var tInt = T.int, tDbl = T.double, tVoidP = ptrT(T.void), tCharP = ptrT(T.char), tLong = T.long, tULong = T.ulong, tFileP = ptrT(T.file);
  var FILE_STDIN = 1000, FILE_STDOUT = 1008, FILE_STDERR = 1016;

  def('stdio.h', 'printf', tInt, [tCharP], function (a) { var b = cformat(readCStr(a[0].v, 'printf format'), a.slice(1), 'printf'); emit(b); return b.length; }, true);
  def('stdio.h', 'fprintf', tInt, [tFileP, tCharP], function (a) { var b = cformat(readCStr(a[1].v, 'fprintf format'), a.slice(2), 'fprintf'); emit(b, a[0].v === FILE_STDERR); return b.length; }, true);
  def('stdio.h', 'sprintf', tInt, [tCharP, tCharP], function (a) { var b = cformat(readCStr(a[1].v, 'sprintf format'), a.slice(2), 'sprintf'); writeBytes(a[0].v, b.concat([0]), 'sprintf'); return b.length; }, true);
  def('stdio.h', 'snprintf', tInt, [tCharP, tULong, tCharP], function (a) { var b = cformat(readCStr(a[2].v, 'snprintf format'), a.slice(3), 'snprintf'); var n = a[1].v; if (n > 0) { var part = b.slice(0, n - 1); writeBytes(a[0].v, part.concat([0]), 'snprintf'); } return b.length; }, true);
  def('stdio.h', 'scanf', tInt, [tCharP], function (a) { return cscanf(readCStr(a[0].v, 'scanf format'), a.slice(1).map(scanTarget), STDIN_SRC); }, true);
  def('stdio.h', 'sscanf', tInt, [tCharP, tCharP], function (a) { return cscanf(readCStr(a[1].v, 'sscanf format'), a.slice(2).map(scanTarget), strSrc(readCStr(a[0].v, 'sscanf'))); }, true);
  def('stdio.h', 'getchar', tInt, [], function () { return INPOS < INPUT.length ? INPUT[INPOS++] : -1; });
  def('stdio.h', 'getc', tInt, [tFileP], function () { return INPOS < INPUT.length ? INPUT[INPOS++] : -1; });
  def('stdio.h', 'fgetc', tInt, [tFileP], function () { return INPOS < INPUT.length ? INPUT[INPOS++] : -1; });
  def('stdio.h', 'ungetc', tInt, [tInt, tFileP], function (a) { if (a[0].v !== -1 && INPOS > 0) INPOS--; return a[0].v; });
  def('stdio.h', 'putchar', tInt, [tInt], function (a) { emit([a[0].v & 255]); return a[0].v & 255; });
  def('stdio.h', 'putc', tInt, [tInt, tFileP], function (a) { emit([a[0].v & 255], a[1].v === FILE_STDERR); return a[0].v & 255; });
  def('stdio.h', 'fputc', tInt, [tInt, tFileP], function (a) { emit([a[0].v & 255], a[1].v === FILE_STDERR); return a[0].v & 255; });
  def('stdio.h', 'puts', tInt, [tCharP], function (a) { emit(readCStr(a[0].v, 'puts').concat([10])); return 1; });
  def('stdio.h', 'fputs', tInt, [tCharP, tFileP], function (a) { emit(readCStr(a[0].v, 'fputs'), a[1].v === FILE_STDERR); return 1; });
  def('stdio.h', 'fgets', tCharP, [tCharP, tInt, tFileP], function (a) {
    var dst = a[0].v, n = a[1].v;
    if (a[2].v !== FILE_STDIN) rt('fgets: only stdin is supported here');
    if (dst === 0) rt('fgets: NULL buffer');
    if (n <= 0) return 0;
    if (INPOS >= INPUT.length) return 0;
    var bytes = [];
    while (bytes.length < n - 1 && INPOS < INPUT.length) { var ch = INPUT[INPOS++]; bytes.push(ch); if (ch === 10) break; }
    bytes.push(0);
    writeBytes(dst, bytes, 'fgets (the size you passed is bigger than the array)');
    return dst;
  });
  def('stdio.h', 'fflush', tInt, [tFileP], function () { return 0; });
  def('stdio.h', 'setbuf', T.void, [tFileP, tCharP], function () { return 0; });
  def('stdio.h', 'feof', tInt, [tFileP], function () { return INPOS >= INPUT.length ? 1 : 0; });
  def('stdio.h', 'perror', T.void, [tCharP], function (a) { emit(readCStr(a[0].v).concat([10]), true); return 0; });

  function heapAlloc(size, zero) {
    if (size < 0 || size !== size) rt('malloc called with a negative size');
    if (size > 16 * 1024 * 1024) return 0;
    var start = alignUp(hTop, 16);
    if (start + size + 32 > MEM) return 0;
    newRegion(start, size, 'heap', 'malloc', LINE);
    hTop = start + size + 32;
    if (zero) { U8.fill(0, start, start + size); IB.fill(1, start, start + size); }
    else IB.fill(0, start, start + size);
    return start;
  }
  function heapFree(p, what) {
    if (p === 0) return;
    var id = SH[p >> 3];
    if (id < 0) {
      var k = -id;
      if (R_KIND[k] === 'heap') rt(what + ': double free - this block (malloc\'d at line ' + R_LINE[k] + ') was already freed at line ' + R_FREEDLINE[k]);
      rt(what + ': pointer to a local variable that no longer exists');
    }
    if (id === 0) rt(what + ': invalid pointer (not something returned by malloc)');
    if (R_KIND[id] !== 'heap') rt(what + ': ' + R_DESC[id] + ' was not allocated with malloc, so it must not be freed');
    if (R_START[id] !== p) rt(what + ': pointer is not the start of a malloc\'d block (it points ' + (p - R_START[id]) + ' bytes inside it)');
    killRegion(id, LINE);
  }
  def('stdlib.h', 'malloc', tVoidP, [tULong], function (a) { return heapAlloc(a[0].v, false); });
  def('stdlib.h', 'calloc', tVoidP, [tULong, tULong], function (a) { return heapAlloc(a[0].v * a[1].v, true); });
  def('stdlib.h', 'realloc', tVoidP, [tVoidP, tULong], function (a) {
    var p = a[0].v, n = a[1].v;
    if (p === 0) return heapAlloc(n, false);
    var id = SH[p >> 3];
    if (id <= 0 || R_KIND[id] !== 'heap' || R_START[id] !== p) heapFree(p, 'realloc');
    var old = R_END[id] - R_START[id];
    var np = heapAlloc(n, false);
    if (np === 0) return 0;
    var m = Math.min(old, n);
    U8.copyWithin(np, p, p + m); IB.copyWithin(np, p, p + m);
    killRegion(id, LINE);
    return np;
  });
  def('stdlib.h', 'free', T.void, [tVoidP], function (a) { heapFree(a[0].v, 'free'); return 0; });
  def('stdlib.h', 'exit', T.void, [tInt], function (a) { throw new ExitSignal(a[0].v | 0); });
  def('stdlib.h', 'abs', tInt, [tInt], function (a) { return Math.abs(a[0].v) | 0; });
  def('stdlib.h', 'labs', tLong, [tLong], function (a) { return Math.abs(a[0].v); });
  def('stdlib.h', 'atoi', tInt, [tCharP], function (a) { var m = /^\s*[+-]?\d+/.exec(bytesToStr(readCStr(a[0].v, 'atoi'))); return m ? parseInt(m[0], 10) | 0 : 0; });
  def('stdlib.h', 'atol', tLong, [tCharP], function (a) { var m = /^\s*[+-]?\d+/.exec(bytesToStr(readCStr(a[0].v, 'atol'))); return m ? parseInt(m[0], 10) : 0; });
  def('stdlib.h', 'atof', tDbl, [tCharP], function (a) { var v = parseFloat(bytesToStr(readCStr(a[0].v, 'atof'))); return v === v ? v : 0; });
  def('stdlib.h', 'rand', tInt, [], function () { RAND_STATE = (Math.imul(RAND_STATE, 1103515245) + 12345) >>> 0; return (RAND_STATE >>> 1) & 0x7fffffff; });
  def('stdlib.h', 'srand', T.void, [T.uint], function (a) { RAND_STATE = a[0].v >>> 0; return 0; });

  function cstrArg(a, i, w) { return readCStr(a[i].v, w); }
  def('string.h', 'strlen', tULong, [tCharP], function (a) { return cstrArg(a, 0, 'strlen').length; });
  def('string.h', 'strcpy', tCharP, [tCharP, tCharP], function (a) { writeBytes(a[0].v, cstrArg(a, 1, 'strcpy').concat([0]), 'strcpy'); return a[0].v; });
  def('string.h', 'strncpy', tCharP, [tCharP, tCharP, tULong], function (a) { var s = cstrArg(a, 1, 'strncpy'), n = a[2].v, out = []; for (var i = 0; i < n; i++) out.push(i < s.length ? s[i] : 0); writeBytes(a[0].v, out, 'strncpy'); return a[0].v; });
  def('string.h', 'strcat', tCharP, [tCharP, tCharP], function (a) { var d = cstrArg(a, 0, 'strcat'), s = cstrArg(a, 1, 'strcat'); writeBytes(a[0].v + d.length, s.concat([0]), 'strcat'); return a[0].v; });
  def('string.h', 'strncat', tCharP, [tCharP, tCharP, tULong], function (a) { var d = cstrArg(a, 0, 'strncat'), s = cstrArg(a, 1, 'strncat').slice(0, a[2].v); writeBytes(a[0].v + d.length, s.concat([0]), 'strncat'); return a[0].v; });
  function cmpBytes(x, y, n) { for (var i = 0; i < n; i++) { var cx = i < x.length ? x[i] : 0, cy = i < y.length ? y[i] : 0; if (cx !== cy) return cx < cy ? -1 : 1; if (cx === 0) return 0; } return 0; }
  def('string.h', 'strcmp', tInt, [tCharP, tCharP], function (a) { var x = cstrArg(a, 0, 'strcmp'), y = cstrArg(a, 1, 'strcmp'); return cmpBytes(x, y, Math.max(x.length, y.length) + 1); });
  def('string.h', 'strncmp', tInt, [tCharP, tCharP, tULong], function (a) { return cmpBytes(cstrArg(a, 0, 'strncmp'), cstrArg(a, 1, 'strncmp'), a[2].v); });
  def('string.h', 'strchr', tCharP, [tCharP, tInt], function (a) { var s = cstrArg(a, 0, 'strchr'), c = a[1].v & 255; if (c === 0) return a[0].v + s.length; var i = s.indexOf(c); return i < 0 ? 0 : a[0].v + i; });
  def('string.h', 'strrchr', tCharP, [tCharP, tInt], function (a) { var s = cstrArg(a, 0, 'strrchr'), c = a[1].v & 255; if (c === 0) return a[0].v + s.length; var i = s.lastIndexOf(c); return i < 0 ? 0 : a[0].v + i; });
  def('string.h', 'strstr', tCharP, [tCharP, tCharP], function (a) { var s = bytesToStr(cstrArg(a, 0, 'strstr')), t = bytesToStr(cstrArg(a, 1, 'strstr')); var hb = cstrArg(a, 0), nb = cstrArg(a, 1); for (var i = 0; i + nb.length <= hb.length; i++) { var ok = true; for (var j = 0; j < nb.length; j++) if (hb[i + j] !== nb[j]) { ok = false; break; } if (ok) return a[0].v + i; } return 0; });
  def('string.h', 'strcspn', tULong, [tCharP, tCharP], function (a) { var s = cstrArg(a, 0, 'strcspn'), r = cstrArg(a, 1, 'strcspn'); for (var i = 0; i < s.length; i++) if (r.indexOf(s[i]) >= 0) return i; return s.length; });
  def('string.h', 'strspn', tULong, [tCharP, tCharP], function (a) { var s = cstrArg(a, 0, 'strspn'), r = cstrArg(a, 1, 'strspn'); for (var i = 0; i < s.length; i++) if (r.indexOf(s[i]) < 0) return i; return s.length; });
  def('string.h', 'memset', tVoidP, [tVoidP, tInt, tULong], function (a) { var n = a[2].v; if (n > 0) { chk(a[0].v, n, 1); U8.fill(a[1].v & 255, a[0].v, a[0].v + n); IB.fill(1, a[0].v, a[0].v + n); } return a[0].v; });
  def('string.h', 'memcpy', tVoidP, [tVoidP, tVoidP, tULong], function (a) { memcopy(a[0].v, a[1].v, a[2].v); return a[0].v; });
  def('string.h', 'memmove', tVoidP, [tVoidP, tVoidP, tULong], function (a) { memcopy(a[0].v, a[1].v, a[2].v); return a[0].v; });
  def('string.h', 'memcmp', tInt, [tVoidP, tVoidP, tULong], function (a) { var n = a[2].v; chk(a[0].v, n, 0); chk(a[1].v, n, 0); for (var i = 0; i < n; i++) { var x = U8[a[0].v + i], y = U8[a[1].v + i]; if (x !== y) return x < y ? -1 : 1; } return 0; });

  function ctype(name, f) { def('ctype.h', name, tInt, [tInt], function (a) { var c = a[0].v; if (c === -1) return 0; if (c < -128 || c > 255) rt(name + ': value ' + c + ' is not a character'); return f(c & 255) ? 1 : 0; }); }
  ctype('isalpha', function (c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122); });
  ctype('isdigit', function (c) { return c >= 48 && c <= 57; });
  ctype('isalnum', function (c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57); });
  ctype('isspace', function (c) { return isSpace(c); });
  ctype('isupper', function (c) { return c >= 65 && c <= 90; });
  ctype('islower', function (c) { return c >= 97 && c <= 122; });
  ctype('ispunct', function (c) { return c > 32 && c < 127 && !((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57)); });
  ctype('isprint', function (c) { return c >= 32 && c < 127; });
  ctype('isxdigit', function (c) { return /[0-9a-fA-F]/.test(String.fromCharCode(c)); });
  def('ctype.h', 'toupper', tInt, [tInt], function (a) { var c = a[0].v; return c >= 97 && c <= 122 ? c - 32 : c; });
  def('ctype.h', 'tolower', tInt, [tInt], function (a) { var c = a[0].v; return c >= 65 && c <= 90 ? c + 32 : c; });

  function m1(name, f) { def('math.h', name, tDbl, [tDbl], function (a) { return f(a[0].v); }); }
  m1('sqrt', Math.sqrt); m1('fabs', Math.abs); m1('floor', Math.floor); m1('ceil', Math.ceil); m1('log', Math.log); m1('log10', Math.log10); m1('log2', Math.log2);
  m1('exp', Math.exp); m1('sin', Math.sin); m1('cos', Math.cos); m1('tan', Math.tan); m1('atan', Math.atan); m1('trunc', Math.trunc);
  m1('round', function (x) { return x < 0 ? -Math.round(-x) : Math.round(x); });
  def('math.h', 'pow', tDbl, [tDbl, tDbl], function (a) { return Math.pow(a[0].v, a[1].v); });
  def('math.h', 'fmod', tDbl, [tDbl, tDbl], function (a) { return a[0].v % a[1].v; });
  def('math.h', 'fmin', tDbl, [tDbl, tDbl], function (a) { return Math.min(a[0].v, a[1].v); });
  def('math.h', 'fmax', tDbl, [tDbl, tDbl], function (a) { return Math.max(a[0].v, a[1].v); });
  def('math.h', 'atan2', tDbl, [tDbl, tDbl], function (a) { return Math.atan2(a[0].v, a[1].v); });
  def('time.h', 'time', tLong, [tVoidP], function () { return 1700000000; });
  def('assert.h', 'assert', T.void, [tInt], null);

  function scanTarget(arg) {
    // arg: {v: address, t: pointer type, conv info attached later}
    return {
      store: function (val) {
        var t = arg.t.to;
        if (arg.v === 0) rt('scanf: NULL pointer passed');
        if (t.k === 'float') storer(t)(arg.v, val);
        else if (t.k === 'int') storer(t)(arg.v, convFn(Number.isInteger(val) ? T.long : T.double, t)(val));
        else rt('scanf: cannot store into this argument');
      },
      storeBytes: function (bytes, term) { writeBytes(arg.v, term ? bytes.concat([0]) : bytes, 'scanf (input is longer than the array - use a width like %99s)'); }
    };
  }

  // printf/scanf format checking at compile time
  function parseFmtSpecs(bytes) {
    var specs = [];
    for (var i = 0; i < bytes.length; i++) {
      if (bytes[i] !== 37) continue;
      i++;
      if (bytes[i] === 37) continue;
      var suppress = false, star = 0;
      if (bytes[i] === 42) { suppress = true; i++; }
      while (i < bytes.length && '-+ #0'.indexOf(String.fromCharCode(bytes[i])) >= 0) i++;
      if (bytes[i] === 42) { star++; i++; } else while (bytes[i] >= 48 && bytes[i] <= 57) i++;
      if (bytes[i] === 46) { i++; if (bytes[i] === 42) { star++; i++; } else while (bytes[i] >= 48 && bytes[i] <= 57) i++; }
      var len = ''; while (i < bytes.length && 'hlLqjzt'.indexOf(String.fromCharCode(bytes[i])) >= 0) len += String.fromCharCode(bytes[i++]);
      var conv = String.fromCharCode(bytes[i]);
      if (conv === '[') { while (i < bytes.length && bytes[i] !== 93) i++; if (bytes[i - 1] === 91 || bytes[i - 1] === 94) { i++; while (i < bytes.length && bytes[i] !== 93) i++; } }
      specs.push({ conv: conv, len: len, suppress: suppress, star: star });
    }
    return specs;
  }

  C.builtinCall = function (n, name, bi) {
    var self = this;
    if (name === 'assert') {
      if (n.args.length !== 1) cerr('assert takes one argument', n);
      var cond = this.truthy(n.args[0]), txt = this.text(n.args[0]);
      return E(T.void, function () { if (!cond()) rt('Assertion failed: ' + txt); return 0; }, { node: n });
    }
    var np = bi.params.length;
    if (n.args.length < np || (!bi.variadic && n.args.length > np)) cerr('too ' + (n.args.length < np ? 'few' : 'many') + " arguments to '" + name + "': expected " + np + (bi.variadic ? ' or more' : '') + ', have ' + n.args.length, n);
    var es = n.args.map(function (a) { return self.rvalue(a); });
    es.forEach(function (e, i) {
      var pt = bi.params[i];
      if (e.t.k === 'struct') cerr('cannot pass a struct to ' + name, n.args[i]);
      if (e.t.k === 'void') cerr('void value passed to ' + name, n.args[i]);
      if (pt) {
        if (pt.k === 'ptr' && pt.to.k === 'struct' && pt.to.opaque) { if (!(e.t.k === 'ptr' && e.t.to.opaque)) cerr("argument " + (i + 1) + " of '" + name + "' must be stdin, stdout or stderr", n.args[i]); return; }
        if (pt.k === 'ptr' && e.t.k !== 'ptr' && !(e.isNull || e.cnst === 0)) cerr("argument " + (i + 1) + " of '" + name + "' should be a pointer" + (pt.to.k === 'int' && pt.to.size === 1 ? ' (a string / char array)' : '') + " but '" + self.text(n.args[i]) + "' has type '" + typeStr(e.t) + "'", n.args[i]);
        if (pt.k !== 'ptr' && e.t.k === 'ptr') cerr("argument " + (i + 1) + " of '" + name + "' should be a number but '" + self.text(n.args[i]) + "' is a pointer '" + typeStr(e.t) + "'", n.args[i]);
      }
    });
    // format checks
    var fmtIdx = { printf: 0, scanf: 0, fprintf: 1, sprintf: 1, snprintf: 2, sscanf: 1 }[name];
    if (fmtIdx !== undefined && n.args[fmtIdx] && n.args[fmtIdx].k === 'str') {
      var isScan = name.indexOf('scanf') >= 0;
      var specs = parseFmtSpecs(n.args[fmtIdx].bytes);
      var ai = fmtIdx + 1;
      specs.forEach(function (sp) {
        if (sp.conv === '%') return;
        if (!isScan) for (var q = 0; q < sp.star; q++) ai++;
        if (sp.suppress && isScan) return;
        var argNode = n.args[ai], e = es[ai];
        if (!argNode) cerr("more '%' conversions than values in " + name + " (no value for %" + sp.len + sp.conv + ')', n.args[fmtIdx]);
        var et = e.t, at = self.text(argNode);
        if (isScan) {
          if (et.k !== 'ptr') cerr("scanf needs the ADDRESS of a variable: write '&" + at + "' instead of '" + at + "'", argNode);
          var to = et.to;
          var c = sp.conv;
          if ('dioux'.indexOf(c) >= 0) {
            var want = sp.len === 'l' || sp.len === 'll' ? 8 : sp.len === 'h' ? 2 : sp.len === 'hh' ? 1 : 4;
            if (to.k !== 'int' || to.size !== want) cerr('%' + sp.len + c + " expects 'int *' but '" + at + "' has type '" + typeStr(et) + "'" + (to.k === 'float' ? ' (use %lf for a double)' : to.size === 1 ? ' (use %c for a char)' : ''), argNode);
          } else if ('feEgG'.indexOf(c) >= 0) {
            if (to.k !== 'float') cerr('%' + sp.len + c + " expects a pointer to " + (sp.len === 'l' ? 'double' : 'float') + " but '" + at + "' has type '" + typeStr(et) + "'" + (to.k === 'int' ? ' (use %d for an int)' : ''), argNode);
            if (sp.len === 'l' && to.size !== 8) cerr("%lf expects 'double *' but '" + at + "' is '" + typeStr(et) + "' (use %f for float)", argNode);
            if (sp.len === '' && to.size !== 4) cerr("%f in scanf reads a float, but '" + at + "' is a double: use %lf", argNode);
          } else if (c === 'c' || c === 's' || c === '[') {
            if (!(to.k === 'int' && to.size === 1)) cerr('%' + c + " expects a 'char *' but '" + at + "' has type '" + typeStr(et) + "'", argNode);
          }
        } else {
          var c2 = sp.conv;
          if ('diouxXc'.indexOf(c2) >= 0) {
            if (et.k === 'float') cerr('%' + sp.len + c2 + " expects an integer but '" + at + "' is a " + typeStr(et) + ' (use %lf or %.2lf to print a double, or cast with (int))', argNode);
            if (et.k === 'ptr') cerr('%' + sp.len + c2 + " expects an integer but '" + at + "' is a pointer '" + typeStr(et) + "'" + (et.to.k === 'int' && et.to.size === 1 ? ' (use %s to print a string)' : ''), argNode);
          } else if ('fFeEgG'.indexOf(c2) >= 0) {
            if (et.k !== 'float') cerr('%' + sp.len + c2 + " expects a double but '" + at + "' has type '" + typeStr(et) + "'" + (et.k === 'int' ? ' (use %d for an int, or (double) to convert)' : ''), argNode);
          } else if (c2 === 's') {
            if (!(et.k === 'ptr' && et.to.k === 'int' && et.to.size === 1)) cerr("%s expects a string (char *) but '" + at + "' has type '" + typeStr(et) + "'" + (et.k === 'int' ? ' (use %c to print one char)' : ''), argNode);
          } else if (c2 === 'p') {
            if (et.k !== 'ptr') cerr("%p expects a pointer", argNode);
          } else cerr("unknown conversion '%" + c2 + "' in format string", n.args[fmtIdx]);
        }
        ai++;
      });
      if (ai < n.args.length) this.warn('more values than % conversions in ' + name + ' format string', n);
    }
    var getters = es.map(function (e) { return e.get; }), types = es.map(function (e) { return e.t; });
    var impl = bi.impl, cnt = getters.length;
    var line = n.line;
    var ret = bi.ret;
    if (name === 'malloc' || name === 'calloc' || name === 'realloc') ret = tVoidP;
    return E(ret, function () {
      var args = new Array(cnt);
      for (var i = 0; i < cnt; i++) args[i] = { v: getters[i](), t: types[i] };
      return impl(args);
    }, { node: n });
  };

  // ------------------------------------------------------------------ run
  function run(src, input, opts) {
    opts = opts || {};
    STEP_LIMIT = opts.stepLimit || 25000000;
    OUT_LIMIT = opts.outputLimit || 1000000;
    resetMachine();
    CUR_SP = STACK_BASE;
    INPUT = typeof input === 'string' ? utf8(input) : (input || []);
    SRC_LINES = src.split('\n');
    var result = { status: 'OK', stdout: '', stderr: '', exitCode: 0, error: null, leaks: [], warnings: [] };
    var comp;
    try {
      var toks = lex(src);
      var pp = preprocess(toks);
      var parser = new Parser(pp.toks, src);
      var items = parser.parseProgram();
      comp = new Compiler(parser, src, pp.includes);
      comp.warnings = parser.warnings.slice();
      // stdin/stdout/stderr globals
      items.forEach(function (it) {
        if (it.k === 'func') comp.compileFunction(it);
        else comp.globalDecl(it);
      });
      if (!comp.funcs.main || !comp.funcs.main.defined) throw new CError('compile', "no 'main' function: every C program needs int main(void) { ... }", 1, 1);
      Object.keys(comp.funcs).forEach(function (k) {
        var F = comp.funcs[k];
        if (!F.defined && F.used) throw new CError('compile', "function '" + k + "' is declared but never defined", F.line, 1);
      });
      result.warnings = comp.warnings;
    } catch (e) {
      if (e instanceof CError) {
        result.status = 'CE';
        result.error = { kind: 'compile', msg: e.msg, line: e.line, col: e.col, text: SRC_LINES[e.line - 1] || '' };
        return result;
      }
      throw e;
    }
    var exitCode = 0;
    try {
      LINE = 0;
      comp.globalInits.forEach(function (f) { f(); });
      comp.staticInits.forEach(function (f) { f(); });
      var mainF = comp.funcs.main;
      var args = [];
      if (mainF.type.params.length >= 1) args.push(1);
      if (mainF.type.params.length >= 2) {
        var progName = comp.strLiteral(utf8('./prog'));
        var argv = heapAlloc(16, true); DV.setFloat64(argv, progName, true); DV.setFloat64(argv + 8, 0, true);
        var aid = SH[argv >> 3]; R_KIND[aid] = 'temp';
        args.push(argv);
      }
      var rv = callUser(mainF, args);
      exitCode = mainF.type.ret.k === 'void' ? 0 : rv | 0;
    } catch (e) {
      if (e instanceof ExitSignal) exitCode = e.code;
      else if (e instanceof CError) {
        result.status = e.kind === 'tle' ? 'TLE' : 'RE';
        result.error = { kind: e.kind, msg: e.msg, line: e.line, col: 0, text: SRC_LINES[e.line - 1] || '' };
      } else if (e instanceof RangeError) {
        result.status = 'RE';
        result.error = { kind: 'runtime', msg: 'stack overflow: recursion too deep (check your base case)', line: LINE, col: 0, text: SRC_LINES[LINE - 1] || '' };
      } else throw e;
    }
    result.exitCode = exitCode;
    result.stdout = bytesToStr(OUT);
    result.stderr = bytesToStr(ERR);
    if (result.status === 'OK') {
      var byLine = {};
      for (var id = 1; id < nRegions; id++) {
        if (R_KIND[id] === 'heap' && SH[R_START[id] >> 3] === id && R_FREEDLINE[id] === 0) {
          var k = R_LINE[id]; byLine[k] = byLine[k] || { line: k, count: 0, bytes: 0 };
          byLine[k].count++; byLine[k].bytes += R_END[id] - R_START[id];
        }
      }
      result.leaks = Object.keys(byLine).map(function (k) { return byLine[k]; });
    }
    return result;
  }

  // stdin/stdout/stderr constants handled in id lookup
  var origExpr = C.expr;
  C.expr = function (n) {
    if (n.k === 'id' && (n.name === 'stdin' || n.name === 'stdout' || n.name === 'stderr') && !this.lookupLocalOnly(n.name)) {
      if (!this.includes['stdio.h']) cerr("use of undeclared identifier '" + n.name + "' (add #include <stdio.h>)", n);
      var v = n.name === 'stdin' ? FILE_STDIN : n.name === 'stdout' ? FILE_STDOUT : FILE_STDERR;
      return E(tFileP, function () { return v; }, { node: n });
    }
    if (n.k === 'call' && n.f.k === 'id') {
      var s = this.lookup(n.f.name);
      if (s && s.kind === 'func') s.F.used = true;
    }
    return origExpr.call(this, n);
  };
  C.lookupLocalOnly = function (name) { for (var s = this.scope; s; s = s.parent) if (Object.prototype.hasOwnProperty.call(s.vars, name)) return true; return false; };

  // mark parenthesised expressions (for '=' in condition warnings)
  var origPrimary = P.parsePrimary;
  P.parsePrimary = function () {
    if (this.is('(') && !this.isTypeStart(this.peek(1))) {
      var e = origPrimary.call(this); e.parens = true; return e;
    }
    return origPrimary.call(this);
  };

  var api = { run: run, version: '1.0' };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  root.CInterp = api;
})(typeof self !== 'undefined' ? self : this);
