'use strict';
(() => {
  /* ================= Utilitas ================= */
  const $ = (s, r = document) => r.querySelector(s);
  const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
  const el = (tag, cls, text) => { const n = document.createElement(tag); if (cls) n.className = cls; if (text != null) n.textContent = text; return n; };
  const clean = (v, max) => String(v || '').replace(/[\u0000-\u001F\u007F<>]/g, '').trim().slice(0, max);
  const pick = (arr) => arr[Math.floor(Math.random() * arr.length)];
  const store = {
    get(k, d) { try { const v = localStorage.getItem(k); return v ? JSON.parse(v) : d; } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) { /* storage tidak tersedia */ } }
  };

  /* ================= Inti aturan catur ================= */
  const FILES = 'abcdefgh';
  const START = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';
  const GLYPH = { k: '♚', q: '♛', r: '♜', b: '♝', n: '♞', p: '♟' };
  const VS = '︎';
  const NAMA = { p: 'pion', n: 'kuda', b: 'gajah', r: 'benteng', q: 'menteri', k: 'raja' };
  const KN = [[-2, -1], [-2, 1], [-1, -2], [-1, 2], [1, -2], [1, 2], [2, -1], [2, 1]];
  const DG = [[-1, -1], [-1, 1], [1, -1], [1, 1]];
  const OR = [[-1, 0], [1, 0], [0, -1], [0, 1]];
  const ALL = DG.concat(OR);
  const isW = (p) => p === p.toUpperCase();
  const colorOf = (p) => (p ? (isW(p) ? 'w' : 'b') : null);
  const sqName = (i) => FILES[i & 7] + (8 - (i >> 3));
  const on = (r, c) => r >= 0 && r < 8 && c >= 0 && c < 8;
  const other = (c) => (c === 'w' ? 'b' : 'w');

  function parseFEN(fen) {
    const [pl, turn, cas, ep, half, full] = fen.trim().split(/\s+/);
    const board = new Array(64).fill(null);
    let i = 0;
    for (const ch of pl) { if (ch === '/') continue; if (/\d/.test(ch)) i += +ch; else board[i++] = ch; }
    const epIdx = ep && ep !== '-' ? (8 - +ep[1]) * 8 + FILES.indexOf(ep[0]) : -1;
    return { board, turn, castling: cas === '-' ? '' : cas, ep: epIdx, half: +half || 0, full: +full || 1 };
  }
  function toFEN(s, counters = true) {
    let out = '';
    for (let r = 0; r < 8; r++) {
      let e = 0;
      for (let c = 0; c < 8; c++) { const p = s.board[r * 8 + c]; if (!p) e++; else { if (e) { out += e; e = 0; } out += p; } }
      if (e) out += e;
      if (r < 7) out += '/';
    }
    out += ' ' + s.turn + ' ' + (s.castling || '-') + ' ' + (s.ep >= 0 ? sqName(s.ep) : '-');
    return counters ? out + ' ' + s.half + ' ' + s.full : out;
  }
  function attacked(b, sq, by) {
    const r = sq >> 3, c = sq & 7, W = by === 'w';
    const P = W ? 'P' : 'p', N = W ? 'N' : 'n', K = W ? 'K' : 'k', B = W ? 'B' : 'b', R = W ? 'R' : 'r', Q = W ? 'Q' : 'q';
    const pr = W ? r + 1 : r - 1;
    for (const dc of [-1, 1]) if (on(pr, c + dc) && b[pr * 8 + c + dc] === P) return true;
    for (const [dr, dc] of KN) if (on(r + dr, c + dc) && b[(r + dr) * 8 + c + dc] === N) return true;
    for (const [dr, dc] of ALL) if (on(r + dr, c + dc) && b[(r + dr) * 8 + c + dc] === K) return true;
    for (const [dr, dc] of DG) { let rr = r + dr, cc = c + dc; while (on(rr, cc)) { const p = b[rr * 8 + cc]; if (p) { if (p === B || p === Q) return true; break; } rr += dr; cc += dc; } }
    for (const [dr, dc] of OR) { let rr = r + dr, cc = c + dc; while (on(rr, cc)) { const p = b[rr * 8 + cc]; if (p) { if (p === R || p === Q) return true; break; } rr += dr; cc += dc; } }
    return false;
  }
  const kingSq = (b, color) => b.indexOf(color === 'w' ? 'K' : 'k');
  const inCheck = (s, color = s.turn) => attacked(s.board, kingSq(s.board, color), other(color));

  function pseudoMoves(s) {
    const b = s.board, me = s.turn, opp = other(me), out = [];
    const add = (f, t, flag = '', promo = null) => out.push({ from: f, to: t, piece: b[f], captured: flag === 'ep' ? (me === 'w' ? 'p' : 'P') : b[t], flag, promo });
    for (let i = 0; i < 64; i++) {
      const p = b[i];
      if (!p || colorOf(p) !== me) continue;
      const t = p.toLowerCase(), r = i >> 3, c = i & 7;
      if (t === 'p') {
        const d = me === 'w' ? -1 : 1, start = me === 'w' ? 6 : 1, last = me === 'w' ? 0 : 7;
        const push = (f, to) => { if ((to >> 3) === last) for (const pr of 'qrbn') add(f, to, '', me === 'w' ? pr.toUpperCase() : pr); else add(f, to); };
        const one = i + d * 8;
        if (on(r + d, c) && !b[one]) { push(i, one); if (r === start && !b[one + d * 8]) add(i, one + d * 8, 'double'); }
        for (const dc of [-1, 1]) {
          if (!on(r + d, c + dc)) continue;
          const to = (r + d) * 8 + c + dc;
          if (b[to] && colorOf(b[to]) !== me) push(i, to);
          else if (to === s.ep && !b[to]) add(i, to, 'ep');
        }
      } else if (t === 'n' || t === 'k') {
        for (const [dr, dc] of (t === 'n' ? KN : ALL)) {
          const rr = r + dr, cc = c + dc;
          if (!on(rr, cc)) continue;
          const to = rr * 8 + cc;
          if (!b[to] || colorOf(b[to]) !== me) add(i, to);
        }
      } else {
        const dirs = t === 'b' ? DG : t === 'r' ? OR : ALL;
        for (const [dr, dc] of dirs) {
          let rr = r + dr, cc = c + dc;
          while (on(rr, cc)) { const to = rr * 8 + cc; if (!b[to]) add(i, to); else { if (colorOf(b[to]) !== me) add(i, to); break; } rr += dr; cc += dc; }
        }
      }
    }
    const cs = s.castling;
    if (me === 'w' && b[60] === 'K' && !attacked(b, 60, opp)) {
      if (cs.includes('K') && b[63] === 'R' && !b[61] && !b[62] && !attacked(b, 61, opp) && !attacked(b, 62, opp)) add(60, 62, 'castleK');
      if (cs.includes('Q') && b[56] === 'R' && !b[59] && !b[58] && !b[57] && !attacked(b, 59, opp) && !attacked(b, 58, opp)) add(60, 58, 'castleQ');
    }
    if (me === 'b' && b[4] === 'k' && !attacked(b, 4, opp)) {
      if (cs.includes('k') && b[7] === 'r' && !b[5] && !b[6] && !attacked(b, 5, opp) && !attacked(b, 6, opp)) add(4, 6, 'castleK');
      if (cs.includes('q') && b[0] === 'r' && !b[3] && !b[2] && !b[1] && !attacked(b, 3, opp) && !attacked(b, 2, opp)) add(4, 2, 'castleQ');
    }
    return out;
  }
  function makeMove(s, m) {
    const b = s.board.slice(), me = s.turn;
    b[m.to] = m.promo || b[m.from];
    b[m.from] = null;
    if (m.flag === 'ep') b[m.to + (me === 'w' ? 8 : -8)] = null;
    if (m.flag === 'castleK') { b[m.to - 1] = b[m.to + 1]; b[m.to + 1] = null; }
    if (m.flag === 'castleQ') { b[m.to + 1] = b[m.to - 2]; b[m.to - 2] = null; }
    let cas = s.castling;
    const strip = (sq) => {
      if (sq === 60) cas = cas.replace(/[KQ]/g, ''); if (sq === 63) cas = cas.replace('K', ''); if (sq === 56) cas = cas.replace('Q', '');
      if (sq === 4) cas = cas.replace(/[kq]/g, ''); if (sq === 7) cas = cas.replace('k', ''); if (sq === 0) cas = cas.replace('q', '');
    };
    strip(m.from); strip(m.to);
    const pawn = m.piece.toLowerCase() === 'p';
    return { board: b, turn: other(me), castling: cas, ep: m.flag === 'double' ? (m.from + m.to) / 2 : -1, half: pawn || m.captured ? 0 : s.half + 1, full: me === 'b' ? s.full + 1 : s.full };
  }
  function legalMoves(s) {
    const me = s.turn, opp = other(me);
    return pseudoMoves(s).filter((m) => { const n = makeMove(s, m); return !attacked(n.board, kingSq(n.board, me), opp); });
  }
  const uciOf = (m) => sqName(m.from) + sqName(m.to) + (m.promo ? m.promo.toLowerCase() : '');
  function toSAN(s, m, legal) {
    let str;
    if (m.flag === 'castleK') str = 'O-O';
    else if (m.flag === 'castleQ') str = 'O-O-O';
    else {
      const t = m.piece.toLowerCase(), cap = !!m.captured;
      if (t === 'p') str = (cap ? FILES[m.from & 7] + 'x' : '') + sqName(m.to) + (m.promo ? '=' + m.promo.toUpperCase() : '');
      else {
        const amb = legal.filter((o) => o.piece === m.piece && o.to === m.to && o.from !== m.from);
        let dis = '';
        if (amb.length) {
          const sameFile = amb.some((o) => (o.from & 7) === (m.from & 7));
          const sameRank = amb.some((o) => (o.from >> 3) === (m.from >> 3));
          dis = !sameFile ? FILES[m.from & 7] : !sameRank ? String(8 - (m.from >> 3)) : sqName(m.from);
        }
        str = t.toUpperCase() + dis + (cap ? 'x' : '') + sqName(m.to);
      }
    }
    const n = makeMove(s, m);
    if (inCheck(n)) str += legalMoves(n).length ? '+' : '#';
    return str;
  }
  function insufficient(b) {
    const pcs = [];
    b.forEach((p, i) => { if (p && p.toLowerCase() !== 'k') pcs.push([p, i]); });
    if (!pcs.length) return true;
    if (pcs.length === 1 && 'nbNB'.includes(pcs[0][0])) return true;
    if (pcs.length === 2 && pcs.every(([p]) => 'bB'.includes(p)) && colorOf(pcs[0][0]) !== colorOf(pcs[1][0])) {
      const sc = (i) => ((i >> 3) + (i & 7)) % 2;
      return sc(pcs[0][1]) === sc(pcs[1][1]);
    }
    return false;
  }
  function gameStatus(s, keys) {
    const lm = legalMoves(s);
    if (!lm.length) return inCheck(s) ? { over: true, type: 'mate', winner: other(s.turn) } : { over: true, type: 'stalemate' };
    if (s.half >= 100) return { over: true, type: 'fifty' };
    if (insufficient(s.board)) return { over: true, type: 'material' };
    const k = toFEN(s, false);
    if (keys.filter((x) => x === k).length >= 3) return { over: true, type: 'repetition' };
    return { over: false };
  }

  /* ================= Bot bawaan (alpha-beta) ================= */
  const VAL = { p: 100, n: 320, b: 330, r: 500, q: 900, k: 0 };
  const PST = {
    p: [0,0,0,0,0,0,0,0,50,50,50,50,50,50,50,50,10,10,20,30,30,20,10,10,5,5,10,25,25,10,5,5,0,0,0,20,20,0,0,0,5,-5,-10,0,0,-10,-5,5,5,10,10,-20,-20,10,10,5,0,0,0,0,0,0,0,0],
    n: [-50,-40,-30,-30,-30,-30,-40,-50,-40,-20,0,0,0,0,-20,-40,-30,0,10,15,15,10,0,-30,-30,5,15,20,20,15,5,-30,-30,0,15,20,20,15,0,-30,-30,5,10,15,15,10,5,-30,-40,-20,0,5,5,0,-20,-40,-50,-40,-30,-30,-30,-30,-40,-50],
    b: [-20,-10,-10,-10,-10,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,0,5,10,10,5,0,-10,-10,5,5,10,10,5,5,-10,-10,0,10,10,10,10,0,-10,-10,10,10,10,10,10,10,-10,-10,5,0,0,0,0,5,-10,-20,-10,-10,-10,-10,-10,-10,-20],
    r: [0,0,0,0,0,0,0,0,5,10,10,10,10,10,10,5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,0,0,0,5,5,0,0,0],
    q: [-20,-10,-10,-5,-5,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,0,5,5,5,5,0,-10,-5,0,5,5,5,5,0,-5,0,0,5,5,5,5,0,-5,-10,5,5,5,5,5,0,-10,-10,0,5,0,0,0,0,-10,-20,-10,-10,-5,-5,-10,-10,-20],
    k: [-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-20,-30,-30,-40,-40,-30,-30,-20,-10,-20,-20,-20,-20,-20,-20,-10,20,20,0,0,0,0,20,20,20,30,10,0,0,10,30,20]
  };
  function evaluate(s) {
    let sc = 0;
    for (let i = 0; i < 64; i++) {
      const p = s.board[i];
      if (!p) continue;
      const t = p.toLowerCase();
      if (isW(p)) sc += VAL[t] + PST[t][i];
      else sc -= VAL[t] + PST[t][(7 - (i >> 3)) * 8 + (i & 7)];
    }
    return s.turn === 'w' ? sc : -sc;
  }
  const orderMoves = (ms) => ms.sort((a, b) => ((b.captured ? VAL[b.captured.toLowerCase()] * 10 - VAL[b.piece.toLowerCase()] : 0) + (b.promo ? 800 : 0)) - ((a.captured ? VAL[a.captured.toLowerCase()] * 10 - VAL[a.piece.toLowerCase()] : 0) + (a.promo ? 800 : 0)));
  function builtinSearch(s, maxDepth, timeMs, randomCp) {
    const t0 = performance.now();
    let nodes = 0, stop = false;
    const MATE = 100000;
    function qs(st, a, b, qd) {
      nodes++;
      const stand = evaluate(st);
      if (stand >= b) return b;
      if (stand > a) a = stand;
      if (qd <= 0) return a;
      const caps = orderMoves(legalMoves(st).filter((m) => m.captured || m.promo));
      for (const m of caps) { const sc = -qs(makeMove(st, m), -b, -a, qd - 1); if (sc >= b) return b; if (sc > a) a = sc; }
      return a;
    }
    function nega(st, d, a, b, ply) {
      if ((++nodes & 511) === 0 && performance.now() - t0 > timeMs) stop = true;
      if (stop) return 0;
      const ms = legalMoves(st);
      if (!ms.length) return inCheck(st) ? -MATE + ply : 0;
      if (d <= 0) return qs(st, a, b, 3);
      orderMoves(ms);
      for (const m of ms) {
        const sc = -nega(makeMove(st, m), d - 1, -b, -a, ply + 1);
        if (stop) return 0;
        if (sc >= b) return b;
        if (sc > a) a = sc;
      }
      return a;
    }
    let root = orderMoves(legalMoves(s));
    if (!root.length) return { move: null, score: 0 };
    let best = root[0], bestScore = 0;
    for (let d = 1; d <= maxDepth; d++) {
      let a = -Infinity, cb = null, cs = -Infinity;
      for (const m of root) {
        const sc = -nega(makeMove(s, m), d - 1, -Infinity, -a, 1);
        if (stop) break;
        if (sc > cs) { cs = sc; cb = m; }
        if (sc > a) a = sc;
      }
      if (stop) break;
      best = cb; bestScore = cs;
      root = [best].concat(root.filter((m) => m !== best));
      if (performance.now() - t0 > timeMs * 0.45) break;
    }
    if (randomCp > 0) {
      const scored = root.map((m) => [m, -qs(makeMove(s, m), -Infinity, Infinity, 2)]);
      const top = Math.max(...scored.map((x) => x[1]));
      const pool = scored.filter((x) => x[1] >= top - randomCp);
      if (pool.length && Math.random() < 0.7) best = pick(pool)[0];
    }
    return { move: best, score: bestScore };
  }

  /* ================= Stockfish (Web Worker) ================= */
  const SF = { w: null, ready: false, listeners: [], chain: Promise.resolve() };
  function initStockfish() {
    return new Promise((resolve) => {
      let done = false;
      const finish = (ok) => { if (done) return; done = true; clearTimeout(timer); resolve(ok); };
      const timer = setTimeout(() => { try { if (SF.w) SF.w.terminate(); } catch (e) { /* abaikan */ } SF.w = null; finish(false); }, 12000);
      try {
        const w = new Worker('engine/stockfish.js');
        SF.w = w;
        w.onmessage = (e) => {
          const line = typeof e.data === 'string' ? e.data : '';
          if (line === 'uciok') { SF.ready = true; finish(true); }
          SF.listeners.slice().forEach((f) => f(line));
        };
        w.onerror = () => { SF.ready = false; finish(false); };
        w.postMessage('uci');
      } catch (e) { finish(false); }
    });
  }
  function sfGo(fen, opt) {
    const job = () => new Promise((resolve) => {
      const info = { cp: 0, mate: null, pv: [], best: null };
      const guard = setTimeout(() => { if (SF.w) SF.w.postMessage('stop'); }, (opt.movetime || 1000) + 6000);
      const fn = (line) => {
        if (line.startsWith('info') && line.includes(' pv ')) {
          const m = line.match(/score (cp|mate) (-?\d+)/);
          if (m) { if (m[1] === 'cp') { info.cp = +m[2]; info.mate = null; } else info.mate = +m[2]; }
          info.pv = line.split(' pv ')[1].trim().split(/\s+/);
        } else if (line.startsWith('bestmove')) {
          clearTimeout(guard);
          SF.listeners = SF.listeners.filter((f) => f !== fn);
          info.best = line.split(/\s+/)[1];
          resolve(info);
        }
      };
      SF.listeners.push(fn);
      SF.w.postMessage('setoption name Skill Level value ' + opt.skill);
      SF.w.postMessage('position fen ' + fen);
      SF.w.postMessage('go' + (opt.depth ? ' depth ' + opt.depth : '') + (opt.movetime ? ' movetime ' + opt.movetime : ''));
    });
    const p = SF.chain.then(job);
    SF.chain = p.catch(() => {});
    return p;
  }
  const scoreToCp = (r) => (r.mate != null ? (r.mate > 0 ? 10000 - r.mate * 10 : -10000 - r.mate * 10) : r.cp);

  /* ================= State aplikasi ================= */
  const LEVEL_NAMES = ['Pemula', 'Pemula+', 'Santai', 'Santai+', 'Menengah', 'Menengah+', 'Kuat', 'Kuat+', 'Master', 'Grandmaster'];
  const settings = Object.assign({ name: 'Pemain', level: 5, engine: 'stockfish', color: 'w', coach: true, evalBar: true, hints: true }, store.get('cm_settings', {}));
  const stats = Object.assign({ win: 0, loss: 0, draw: 0, streak: 0, accSum: 0, accN: 0 }, store.get('cm_stats', {}));
  const G = { states: [], moves: [], keys: [], player: 'w', over: null, token: 0, busy: false, analysis: null, losses: [], opening: '' };
  let selected = -1, targets = [], hintSq = [], flipped = false, sfOk = false;

  /* ================= Toast & Modal ================= */
  function toast(msg, err) {
    const t = el('div', 'toast' + (err ? ' err' : ''), msg);
    $('#toasts').appendChild(t);
    setTimeout(() => { t.classList.add('out'); setTimeout(() => t.remove(), 300); }, 2600);
  }
  function openDlg(id) { const d = document.getElementById(id); if (d && !d.open) d.showModal(); }
  function confirmBox(title, text, yesLabel) {
    return new Promise((resolve) => {
      const d = $('#dlgConfirm');
      $('#cfTitle').textContent = title;
      $('#cfText').textContent = text;
      $('#cfYes').textContent = yesLabel || 'Ya';
      $('#cfNo').hidden = yesLabel === null;
      const done = (v) => { d.close(); $('#cfYes').onclick = null; $('#cfNo').onclick = null; d.onclose = null; resolve(v); };
      $('#cfYes').onclick = () => done(true);
      $('#cfNo').onclick = () => done(false);
      d.onclose = () => resolve(false);
      d.showModal();
    });
  }
  function infoBox(title, text) {
    const d = $('#dlgConfirm');
    $('#cfTitle').textContent = title;
    $('#cfText').textContent = text;
    $('#cfYes').textContent = 'Oke';
    $('#cfNo').hidden = true;
    $('#cfYes').onclick = () => d.close();
    d.onclose = () => { $('#cfNo').hidden = false; };
    if (!d.open) d.showModal();
  }
  function choosePromotion(color) {
    return new Promise((resolve) => {
      const d = $('#dlgPromo'), grid = $('#promoGrid');
      grid.replaceChildren();
      let chosen = null;
      for (const t of ['q', 'r', 'b', 'n']) {
        const b = el('button', 'promo-btn');
        b.type = 'button';
        b.setAttribute('aria-label', NAMA[t]);
        const sp = el('span', 'pc ' + color, GLYPH[t] + VS);
        b.appendChild(sp);
        b.addEventListener('click', () => { chosen = color === 'w' ? t.toUpperCase() : t; d.close(); });
        grid.appendChild(b);
      }
      d.onclose = () => { d.onclose = null; resolve(chosen); };
      d.showModal();
    });
  }

  /* ================= Mentor AI ================= */
  const chat = $('#chat');
  function say(text, who = 'bot', tag, tagCls) {
    const li = el('li', 'msg ' + who);
    if (tag) { li.appendChild(el('span', 'tag ' + (tagCls || ''), tag)); li.appendChild(document.createElement('br')); }
    li.appendChild(document.createTextNode(text));
    chat.appendChild(li);
    while (chat.children.length > 80) chat.firstChild.remove();
    chat.scrollTop = chat.scrollHeight;
    return li;
  }
  const OPENINGS = [
    ['e4 e5 Nf3 Nc6 Bb5', 'Ruy Lopez (Spanyol)', 'Tekan kuda c6 yang melindungi e5. Klasik banget.'],
    ['e4 e5 Nf3 Nc6 Bc4', 'Italian Game', 'Gajah bidik f7, titik paling rapuh hitam.'],
    ['e4 e5 Nf3 Nc6 d4', 'Scotch Game', 'Buka tengah lebih cepat, permainan jadi terbuka.'],
    ['e4 e5 Nf3 d6', 'Philidor Defense', 'Solid tapi agak pasif, hati-hati ruang gerak.'],
    ['e4 e5 f4', "King's Gambit", 'Gambit agresif: korbankan pion demi serangan.'],
    ['e4 e5', 'Open Game', 'Duel pion tengah, cocok untuk latihan taktik.'],
    ['e4 c5', 'Sicilian Defense', 'Pertahanan paling tajam lawan e4. Penuh serangan balik.'],
    ['e4 e6', 'French Defense', 'Struktur kokoh; incar serangan balik di d5.'],
    ['e4 c6', 'Caro-Kann', 'Aman dan rapi, favorit pemain posisional.'],
    ['e4 d5', 'Scandinavian Defense', 'Langsung tantang e4. Waspadai menteri yang keluar terlalu awal.'],
    ['d4 d5 c4', "Queen's Gambit", 'Tawarkan pion c4 untuk menguasai pusat.'],
    ['d4 d5 Bf4', 'London System', 'Setup sederhana dan solid, mudah dihafal.'],
    ['d4 Nf6 Bf4', 'London System', 'Setup sederhana dan solid, mudah dihafal.'],
    ['d4 Nf6 c4 g6', "King's Indian Defense", 'Biarkan putih ambil pusat, lalu serang balik.'],
    ['d4 Nf6 c4 e6', 'Indian Defense (e6)', 'Fleksibel: bisa ke Nimzo-Indian atau Queen\'s Indian.'],
    ['d4 d5', "Queen's Pawn Game", 'Pertarungan pusat yang lebih tenang.'],
    ['c4', 'English Opening', 'Kuasai d5 dari sayap, gaya posisional.'],
    ['Nf3', 'Réti Opening', 'Fleksibel, putuskan struktur pion belakangan.']
  ];
  function detectOpening() {
    const seq = G.moves.slice(0, 10).map((m) => m.san.replace(/[+#]/g, '')).join(' ');
    let found = null;
    for (const o of OPENINGS) if ((seq + ' ').startsWith(o[0] + ' ') && (!found || o[0].length > found[0].length)) found = o;
    return found;
  }
  const TIPS = [
    'Kuasai pusat (e4, d4, e5, d5) di awal game. Pusat = kontrol.',
    'Keluarkan kuda dan gajah dulu sebelum menteri. Jangan buru-buru solo karier pakai menteri 😅',
    'Rokade cepat biar raja aman, terus hubungkan kedua benteng.',
    'Sebelum melangkah, cek 3 hal: skak, makan, ancaman. Selalu!',
    'Setiap langkah lawan punya maksud. Tanya dulu: "dia mau ngapain?"',
    'Benteng suka file terbuka, taruh di sana.',
    'Di endgame, raja itu bidak penyerang. Majukan ke tengah.',
    'Jangan gerakkan bidak yang sama dua kali di pembukaan tanpa alasan kuat.',
    'Kalau unggul materi, tukar bidak. Kalau tertinggal, hindari tukar.',
    'Pion lewat (passed pawn) harus didorong, apalagi di endgame.'
  ];
  function describeEval(cpWhite, mateWhite) {
    const meSign = G.player === 'w' ? 1 : -1;
    if (mateWhite != null) {
      const mine = mateWhite * meSign > 0;
      return mine ? 'Ada skakmat paksa untukmu dalam ' + Math.abs(mateWhite) + ' langkah! Cari terus 🔥' : 'Bahaya: robot punya skakmat paksa dalam ' + Math.abs(mateWhite) + ' langkah. Bertahan sekuat tenaga!';
    }
    const v = cpWhite * meSign / 100;
    const abs = Math.abs(v).toFixed(1);
    if (Math.abs(v) < 0.4) return 'Posisi seimbang (' + (v >= 0 ? '+' : '') + v.toFixed(1) + '). Masih 50:50, siapa lebih teliti dia menang.';
    if (v > 0) return v > 3 ? 'Kamu unggul jauh (+' + abs + ')! Tinggal konversi, jangan lengah.' : 'Kamu sedikit unggul (+' + abs + '). Pertahankan tekanannya.';
    return v < -3 ? 'Kamu tertinggal jauh (−' + abs + '). Cari peluang taktik atau jebakan.' : 'Robot sedikit unggul (−' + abs + '). Masih bisa dibalik!';
  }
  function moveHuman(s, m) {
    if (m.flag === 'castleK') return 'rokade pendek';
    if (m.flag === 'castleQ') return 'rokade panjang';
    return NAMA[m.piece.toLowerCase()] + ' ke ' + sqName(m.to) + (m.captured ? ' (makan ' + NAMA[m.captured.toLowerCase()] + ')' : '');
  }
  function answer(q) {
    const t = q.toLowerCase();
    const name = settings.name || 'Pemain';
    if (/saran|hint|bantu|terbaik|best|langkah apa/.test(t)) { showHint(); return null; }
    if (/eval|posisi|unggul|skor|siapa menang/.test(t)) {
      if (G.analysis && G.analysis.ply === G.moves.length) return describeEval(G.analysis.cpWhite, G.analysis.mateWhite);
      requestAnalysis(true);
      return 'Bentar, aku hitung dulu posisinya…';
    }
    if (/pembuka|opening/.test(t)) {
      const o = detectOpening();
      return o ? 'Ini ' + o[1] + '. ' + o[2] : 'Belum ada nama pembukaan yang cocok. Coba mulai dengan e4 atau d4, keduanya solid untuk belajar.';
    }
    if (/rokade|castl/.test(t)) return 'Rokade: raja geser 2 petak ke arah benteng, benteng loncat ke sisi sebelahnya. Syarat: raja & benteng belum pernah gerak, petak di antara kosong, dan raja tidak sedang/akan melewati petak yang diskak. Di sini: ketuk raja, lalu ketuk petak tujuannya (g1/c1).';
    if (/en ?passant/.test(t)) return 'En passant: kalau pion lawan maju 2 petak dan mendarat tepat di samping pionmu, kamu boleh memakannya seolah ia maju 1 petak — tapi hanya pada langkah berikutnya.';
    if (/promosi|promote/.test(t)) return 'Promosi: pion yang sampai baris terakhir berubah jadi menteri, benteng, gajah, atau kuda. Biasanya pilih menteri, kecuali ada trik skakmat pakai kuda.';
    if (/skakmat|checkmate|stalemate|remis|draw/.test(t)) return 'Skakmat = raja diskak dan tidak bisa kabur → game selesai. Stalemate = tidak ada langkah legal tapi raja tidak diskak → remis. Remis juga terjadi lewat pengulangan 3x, aturan 50 langkah, atau materi tidak cukup.';
    if (/stockfish|engine|robot|bot/.test(t)) return sfOk ? 'Lawanmu memakai Stockfish 10 yang jalan langsung di browser (WebAssembly). Level 1–10 mengatur Skill Level & waktu pikirnya. Ubah di Pengaturan.' : 'Stockfish belum aktif, jadi lawanmu sekarang bot bawaan (alpha-beta). Tetap bisa diatur levelnya di Pengaturan.';
    if (/level|susah|sulit|gampang|mudah/.test(t)) return 'Level robot sekarang ' + settings.level + ' (' + LEVEL_NAMES[settings.level - 1] + '). Ganti lewat menu Pengaturan — berlaku langsung di langkah berikutnya.';
    if (/undo|batal|ulang/.test(t)) return 'Tekan tombol Undo untuk membatalkan langkah terakhirmu (sekalian langkah robot). Belajar dari salah itu sah kok.';
    if (/tips|belajar|gimana|cara|menang/.test(t)) return pick(TIPS);
    if (/makasih|terima kasih|thanks|thx/.test(t)) return 'Sama-sama, ' + name + '! Gas lanjut 💪';
    if (/halo|hai|hi\b|hello|pagi|siang|sore|malam|hey/.test(t)) return 'Halo ' + name + '! Aku Nara, mentor caturmu. Mau latihan apa hari ini?';
    return 'Aku mentor offline, jadi paham topik catur saja. Coba tanya: "saran", "evaluasi", "pembukaan", "rokade", "en passant", "promosi", atau "tips".';
  }

  /* ================= Render ================= */
  const boardEl = $('#board');
  const cur = () => G.states[G.states.length - 1];
  const orientationBlack = () => (G.player === 'b') !== flipped;

  function render() {
    const s = cur();
    const last = G.moves.length ? G.moves[G.moves.length - 1].m : null;
    const chk = inCheck(s) ? kingSq(s.board, s.turn) : -1;
    const blackView = orientationBlack();
    const frag = document.createDocumentFragment();
    for (let v = 0; v < 64; v++) {
      const i = blackView ? 63 - v : v;
      const r = i >> 3, c = i & 7;
      const btn = el('button', 'sq ' + ((r + c) % 2 ? 'dark' : 'light'));
      btn.type = 'button';
      btn.dataset.sq = String(i);
      const p = s.board[i];
      btn.setAttribute('aria-label', sqName(i) + (p ? ' ' + NAMA[p.toLowerCase()] + (isW(p) ? ' putih' : ' hitam') : ''));
      if (last && (i === last.from || i === last.to)) btn.classList.add('last');
      if (i === selected) btn.classList.add('sel');
      if (hintSq.includes(i)) btn.classList.add('hint');
      if (i === chk) btn.classList.add('check');
      if (targets.includes(i) && settings.hints) { btn.classList.add('target'); if (p || (s.ep === i)) btn.classList.add('cap'); }
      if (p) btn.appendChild(el('span', 'pc ' + colorOf(p) + (colorOf(p) === G.player ? ' mine' : ''), GLYPH[p.toLowerCase()] + VS));
      if ((blackView ? r === 0 : r === 7)) btn.appendChild(el('span', 'coord f', FILES[c]));
      if ((blackView ? c === 7 : c === 0)) btn.appendChild(el('span', 'coord r', String(8 - r)));
      frag.appendChild(btn);
    }
    boardEl.replaceChildren(frag);
    if (G.anim) { const a = G.anim; G.anim = null; animateMove(a); }
    renderCaptured();
    renderMoves();
    renderStatus();
    renderPlayers();
  }
  function renderCaptured() {
    const s = cur();
    const startCount = { p: 8, n: 2, b: 2, r: 2, q: 1 };
    const count = { w: {}, b: {} };
    s.board.forEach((p) => { if (p && p.toLowerCase() !== 'k') { const c = colorOf(p); count[c][p.toLowerCase()] = (count[c][p.toLowerCase()] || 0) + 1; } });
    const lost = (c) => { let str = '', val = 0; for (const t of ['q', 'r', 'b', 'n', 'p']) { const n = Math.max(0, startCount[t] - (count[c][t] || 0)); str += (GLYPH[t] + VS).repeat(n); val += n * VAL[t]; } return { str, val }; };
    const lw = lost('w'), lb = lost('b');
    const me = G.player;
    const meTook = me === 'w' ? lb : lw, botTook = me === 'w' ? lw : lb;
    const fill = (node, took, theirs) => {
      node.replaceChildren(document.createTextNode(took.str));
      const diff = Math.round((took.val - theirs.val) / 100);
      if (diff > 0) node.appendChild(el('span', 'adv', '+' + diff));
    };
    fill($('#capBottom'), meTook, botTook);
    fill($('#capTop'), botTook, meTook);
  }
  function renderMoves() {
    const list = $('#moveList');
    list.replaceChildren();
    for (let i = 0; i < G.moves.length; i += 2) {
      const li = el('li');
      li.appendChild(el('span', 'no', (i / 2 + 1) + '.'));
      const a = el('span', 'mv' + (i === G.moves.length - 1 ? ' cur' : ''), G.moves[i].san);
      const b = el('span', 'mv' + (i + 1 === G.moves.length - 1 ? ' cur' : ''), G.moves[i + 1] ? G.moves[i + 1].san : '');
      li.append(a, b);
      list.appendChild(li);
    }
    list.scrollTop = list.scrollHeight;
    const o = detectOpening();
    $('#openingName').textContent = o ? o[1] : 'Belum terdeteksi';
  }
  function renderStatus() {
    const s = cur();
    let txt;
    if (G.over) txt = resultText(G.over);
    else if (G.busy) txt = 'Robot sedang berpikir…';
    else txt = (s.turn === G.player ? 'Giliranmu' : 'Giliran robot') + (inCheck(s) ? ' — SKAK!' : '.');
    $('#statusLine').textContent = txt;
    $('#btnUndo').disabled = G.busy || G.moves.length === 0;
    $('#btnHint').disabled = G.busy || !!G.over;
    $('#btnResign').disabled = !!G.over || G.moves.length === 0;
  }
  function renderPlayers() {
    const name = settings.name || 'Pemain';
    $('#meLabel').textContent = name;
    $('#heroName').textContent = name;
    $('#meMeta').textContent = G.player === 'w' ? 'Putih' : 'Hitam';
    $('#botLabel').textContent = sfOk && settings.engine === 'stockfish' ? 'Robot AI · Stockfish' : 'Robot AI · Bawaan';
    $('#botMeta').textContent = 'Level ' + settings.level + ' · ' + LEVEL_NAMES[settings.level - 1] + ' · ' + (G.player === 'w' ? 'Hitam' : 'Putih');
    $('#evalBar').classList.toggle('is-off', !settings.evalBar);
    $('.board-wrap').classList.toggle('no-eval', !settings.evalBar);
  }
  function renderEval(cpWhite, mateWhite) {
    const blackView = orientationBlack();
    let pct;
    if (mateWhite != null) pct = mateWhite > 0 ? 100 : 0;
    else pct = 100 / (1 + Math.exp(-cpWhite / 300));
    $('#evalFill').style.height = pct.toFixed(1) + '%';
    $('#evalBar').classList.toggle('flip', blackView);
    $('#evalText').textContent = mateWhite != null ? 'M' + Math.abs(mateWhite) : ((cpWhite >= 0 ? '+' : '') + (cpWhite / 100).toFixed(1));
    $('#evalBar').setAttribute('aria-label', 'Evaluasi ' + $('#evalText').textContent + ' untuk putih');
  }
  function renderStats() {
    $('#stWin').textContent = stats.win; $('#stLoss').textContent = stats.loss; $('#stDraw').textContent = stats.draw; $('#stStreak').textContent = stats.streak;
    const acc = stats.accN ? Math.round(stats.accSum / stats.accN) : null;
    $('#accFill').style.width = (acc || 0) + '%';
    $('#accText').textContent = acc == null ? 'Belum ada data' : acc + '% dari ' + stats.accN + ' game';
  }
  function setEngineStatus(text, cls) {
    $('#engineStatus').textContent = text;
    $('#engineDot').className = 'dot ' + (cls || '');
  }
  function resultText(o) {
    if (o.type === 'mate') return o.winner === G.player ? 'Skakmat! Kamu menang 🏆' : 'Skakmat. Robot menang.';
    if (o.type === 'resign') return 'Kamu menyerah. Robot menang.';
    return { stalemate: 'Remis — stalemate.', fifty: 'Remis — aturan 50 langkah.', material: 'Remis — materi tidak cukup.', repetition: 'Remis — pengulangan 3 kali.' }[o.type] || 'Game selesai.';
  }

  /* ================= Alur permainan ================= */
  function saveGame() {
    store.set('cm_game', { player: G.player, moves: G.moves.map((x) => x.uci), over: G.over ? G.over : null, losses: G.losses });
  }
  function newGame(colorPref) {
    G.token++;
    if (SF.w && sfOk) SF.w.postMessage('stop');
    const c = colorPref === 'r' ? (Math.random() < 0.5 ? 'w' : 'b') : colorPref;
    const s0 = parseFEN(START);
    Object.assign(G, { states: [s0], moves: [], keys: [toFEN(s0, false)], player: c, over: null, busy: false, analysis: null, losses: [], opening: '' });
    selected = -1; targets = []; hintSq = []; flipped = false;
    renderEval(0, null);
    render();
    saveGame();
    say(c === 'w' ? 'Game baru! Kamu pegang putih, silakan buka duluan. Semangat ' + (settings.name || 'Pemain') + '!' : 'Game baru! Kamu pegang hitam. Robot jalan duluan, siap-siap ya.');
    afterTurnChange();
  }
  function applyMove(m, noAnim) {
    const s = cur();
    G.anim = noAnim ? null : { from: m.from, to: m.to, captured: m.captured, capSq: m.flag === 'ep' ? m.to + (s.turn === 'w' ? 8 : -8) : m.to, rook: m.flag === 'castleK' ? [m.to + 1, m.to - 1] : m.flag === 'castleQ' ? [m.to - 2, m.to + 1] : null };
    const legal = legalMoves(s);
    const san = toSAN(s, m, legal);
    const ns = makeMove(s, m);
    G.states.push(ns);
    G.moves.push({ m, san, uci: uciOf(m) });
    G.keys.push(toFEN(ns, false));
    hintSq = [];
    const st = gameStatus(ns, G.keys);
    if (st.over) G.over = st;
    saveGame();
    return { prev: s, next: ns, san };
  }
  async function userMove(m, noAnim) {
    if (m.promo === 'Q' || m.promo === 'q') {
      const pr = await choosePromotion(G.player);
      if (!pr) { selected = -1; targets = []; render(); return; }
      m = legalMoves(cur()).find((x) => x.from === m.from && x.to === m.to && x.promo === pr) || m;
    }
    selected = -1; targets = [];
    const baseline = G.analysis && G.analysis.ply === G.moves.length ? G.analysis : null;
    const { prev, next, san } = applyMove(m, noAnim);
    render();
    const token = G.token;
    const ply = G.moves.length;
    reviewMove(prev, m, san, next, baseline, token, ply).catch(() => {});
    if (G.over) return finishGame();
    afterTurnChange();
  }
  function afterTurnChange() {
    if (G.over) return;
    if (cur().turn !== G.player) botMove();
    else requestAnalysis(false);
  }
  async function engineAnalyse(s, depth, movetime) {
    if (sfOk) {
      const r = await sfGo(toFEN(s), { skill: 20, depth, movetime });
      return { best: r.best, cp: scoreToCp(r), mate: r.mate };
    }
    await new Promise((r) => setTimeout(r, 30));
    const r = builtinSearch(s, 3, Math.min(movetime, 600), 0);
    return { best: r.move ? uciOf(r.move) : null, cp: Math.abs(r.score) > 50000 ? Math.sign(r.score) * 10000 : r.score, mate: null };
  }
  async function requestAnalysis(announce) {
    const token = G.token, ply = G.moves.length, s = cur();
    if (G.over) return;
    const r = await engineAnalyse(s, 12, 700);
    if (token !== G.token || ply !== G.moves.length) return;
    const sign = s.turn === 'w' ? 1 : -1;
    G.analysis = { ply, best: r.best, cp: r.cp, cpWhite: r.cp * sign, mateWhite: r.mate != null ? r.mate * sign : null };
    renderEval(G.analysis.cpWhite, G.analysis.mateWhite);
    if (announce) say(describeEval(G.analysis.cpWhite, G.analysis.mateWhite));
  }
  async function reviewMove(prev, m, san, next, baseline, token, ply) {
    const r = await engineAnalyse(next, 10, 450);
    if (token !== G.token) return;
    const signNext = next.turn === 'w' ? 1 : -1;
    if (ply === G.moves.length) renderEval(r.cp * signNext, r.mate != null ? r.mate * signNext : null);
    const after = -r.cp;
    let loss = null, bestSan = null;
    if (baseline) {
      loss = Math.max(0, baseline.cp - after);
      if (baseline.best && baseline.best !== uciOf(m)) {
        const bm = legalMoves(prev).find((x) => uciOf(x) === baseline.best);
        if (bm) bestSan = toSAN(prev, bm, legalMoves(prev));
      }
      G.losses.push(Math.min(loss, 1000));
      saveGame();
    }
    if (!settings.coach) return;
    const o = detectOpening();
    if (o && o[1] !== G.opening) { G.opening = o[1]; say('📖 ' + o[1] + ' — ' + o[2]); }
    if (G.over && G.over.type === 'mate') return;
    if (loss == null) return;
    let tag, cls, text;
    if (!bestSan || loss <= 15) { tag = 'Langkah terbaik'; cls = 'best'; text = pick(['W move! ' + san + ' persis pilihan engine.', san + ' — mantap, itu langkah terbaik.', 'Gila sih, ' + san + ' = pilihan Stockfish. Gas terus!']); }
    else if (loss <= 50) { tag = 'Bagus'; cls = 'good'; text = san + ' oke banget. Alternatif engine: ' + bestSan + '.'; }
    else if (loss <= 120) { tag = 'Kurang akurat'; cls = 'inacc'; text = san + ' agak kurang presisi (−' + (loss / 100).toFixed(1) + '). Lebih tajam: ' + bestSan + '.'; }
    else if (loss <= 300) { tag = 'Kesalahan'; cls = 'mistake'; text = 'Hmm, ' + san + ' melepas keunggulan (−' + (loss / 100).toFixed(1) + '). Seharusnya ' + bestSan + '. Cek lagi ancaman lawan sebelum jalan.'; }
    else { tag = 'Blunder'; cls = 'blunder'; text = 'Aduh, ' + san + ' blunder (−' + (loss / 100).toFixed(1) + ') 😬 Langkah terbaik tadi ' + bestSan + '. Mau pakai Undo buat coba lagi?'; }
    if (cls === 'best' || cls === 'good') {
      if (m.flag.startsWith('castle')) text += ' Raja aman, benteng aktif 🛡️';
      else if (san.includes('+')) text += ' Skak yang bikin lawan repot.';
    }
    say(text, 'bot', tag, cls);
  }
  async function botMove() {
    if (G.over) return;
    const token = G.token;
    G.busy = true; renderStatus();
    const s = cur();
    const lv = settings.level;
    let uci = null;
    const t0 = performance.now();
    try {
      if (sfOk && settings.engine === 'stockfish') {
        const depth = [1, 2, 3, 5, 7, 9, 11, 13, 16, 20][lv - 1];
        const r = await sfGo(toFEN(s), { skill: Math.round((lv - 1) * 20 / 9), depth, movetime: 250 + lv * 150 });
        uci = r.best;
      } else {
        await new Promise((r) => setTimeout(r, 60));
        const depth = lv <= 2 ? 1 : lv <= 5 ? 2 : lv <= 8 ? 3 : 4;
        const rand = [300, 200, 120, 80, 50, 30, 0, 0, 0, 0][lv - 1];
        const r = builtinSearch(s, depth, 300 + lv * 180, rand);
        uci = r.move ? uciOf(r.move) : null;
      }
    } catch (e) { uci = null; }
    const wait = 350 - (performance.now() - t0);
    if (wait > 0) await new Promise((r) => setTimeout(r, wait));
    if (token !== G.token) return;
    G.busy = false;
    let m = uci ? legalMoves(s).find((x) => uciOf(x) === uci) : null;
    if (!m) { const lm = legalMoves(s); m = lm.length ? lm[0] : null; }
    if (!m) { render(); return; }
    applyMove(m);
    render();
    if (G.over) return finishGame();
    afterTurnChange();
  }
  function finishGame() {
    const o = G.over;
    render();
    let res = 'draw';
    if (o.type === 'mate' || o.type === 'resign') res = o.winner === G.player ? 'win' : 'loss';
    if (res === 'win') { stats.win++; stats.streak++; } else if (res === 'loss') { stats.loss++; stats.streak = 0; } else stats.draw++;
    let summary = '';
    if (G.losses.length) {
      const avg = G.losses.reduce((a, b) => a + b, 0) / G.losses.length;
      const acc = Math.max(5, Math.min(100, Math.round(100 * Math.exp(-avg / 160))));
      stats.accSum += acc; stats.accN++;
      const bl = G.losses.filter((x) => x > 300).length, mi = G.losses.filter((x) => x > 120 && x <= 300).length;
      summary = '\n\nAkurasi kamu: ~' + acc + '%. Blunder: ' + bl + ', kesalahan: ' + mi + '.';
    }
    store.set('cm_stats', stats);
    renderStats();
    saveGame();
    const mentor = res === 'win' ? 'GG! Kemenangan yang layak. Coba naikkan level biar makin tertantang 🔥' : res === 'loss' ? 'Kalah itu bagian dari belajar. Cek tab Langkah dan cari momen yang berubah arah.' : 'Remis! Hasil yang terhormat lawan mesin.';
    say(resultText(o) + ' ' + mentor + summary.replace(/\n\n/, ' '));
    infoBox(resultText(o), mentor + summary);
  }
  async function showHint() {
    if (G.over) { say('Game sudah selesai. Mulai game baru dulu ya.'); return; }
    if (cur().turn !== G.player || G.busy) { toast('Tunggu giliranmu dulu.'); return; }
    if (!G.analysis || G.analysis.ply !== G.moves.length) {
      const thinking = say('Lagi menganalisis…', 'bot');
      thinking.classList.add('typing');
      await requestAnalysis(false);
      thinking.remove();
    }
    const a = G.analysis;
    if (!a || a.ply !== G.moves.length || !a.best) return;
    const s = cur();
    const m = legalMoves(s).find((x) => uciOf(x) === a.best);
    if (!m) return;
    hintSq = [m.from, m.to];
    render();
    say('💡 Coba ' + toSAN(s, m, legalMoves(s)) + ' — ' + moveHuman(s, m) + '. ' + describeEval(a.cpWhite, a.mateWhite));
  }
  function onSquare(i) {
    if (G.over) { toast('Game selesai. Tekan Game Baru untuk main lagi.'); return; }
    const s = cur();
    if (s.turn !== G.player || G.busy) { toast('Sabar, robot lagi mikir 🤖'); return; }
    if (selected >= 0 && targets.includes(i)) {
      const lm = legalMoves(s).filter((x) => x.from === selected && x.to === i);
      const m = lm.find((x) => x.promo && x.promo.toLowerCase() === 'q') || lm[0];
      if (m) { userMove(m); return; }
    }
    const p = s.board[i];
    if (p && colorOf(p) === G.player && i !== selected) {
      selected = i;
      targets = legalMoves(s).filter((x) => x.from === i).map((x) => x.to);
      if (!targets.length) toast('Bidak ini tidak punya langkah legal.');
    } else { selected = -1; targets = []; }
    render();
  }
  function undo() {
    if (G.busy || !G.moves.length) return;
    G.token++;
    if (SF.w && sfOk) SF.w.postMessage('stop');
    let n = cur().turn === G.player ? 2 : 1;
    if (G.over && cur().turn !== G.player) n = 1;
    n = Math.min(n, G.moves.length);
    if (G.moves.length - n === 0 && G.player === 'b') n = Math.max(0, G.moves.length - 1);
    if (n <= 0) { toast('Tidak ada langkahmu untuk dibatalkan.'); return; }
    for (let k = 0; k < n; k++) { G.states.pop(); G.moves.pop(); G.keys.pop(); }
    const userUndone = Math.ceil(n / 2);
    G.losses.splice(Math.max(0, G.losses.length - userUndone), userUndone);
    G.over = null; G.analysis = null; selected = -1; targets = []; hintSq = [];
    render();
    saveGame();
    toast('Langkah dibatalkan.');
    afterTurnChange();
  }
  function pgn() {
    const date = new Date();
    const d = date.getFullYear() + '.' + String(date.getMonth() + 1).padStart(2, '0') + '.' + String(date.getDate()).padStart(2, '0');
    const me = settings.name || 'Pemain', bot = 'Robot AI Level ' + settings.level;
    let result = '*';
    if (G.over) result = G.over.type === 'mate' || G.over.type === 'resign' ? (G.over.winner === 'w' ? '1-0' : '0-1') : '1/2-1/2';
    const head = '[Event "Chess Mentor"]\n[Date "' + d + '"]\n[White "' + (G.player === 'w' ? me : bot) + '"]\n[Black "' + (G.player === 'b' ? me : bot) + '"]\n[Result "' + result + '"]\n\n';
    let body = '';
    G.moves.forEach((x, i) => { if (i % 2 === 0) body += (i / 2 + 1) + '. '; body += x.san + ' '; });
    return head + body + result;
  }
  function restore() {
    const saved = store.get('cm_game', null);
    if (!saved || !Array.isArray(saved.moves) || saved.moves.length === 0 || saved.over) return false;
    const s0 = parseFEN(START);
    Object.assign(G, { states: [s0], moves: [], keys: [toFEN(s0, false)], player: saved.player === 'b' ? 'b' : 'w', over: null, busy: false, analysis: null, losses: Array.isArray(saved.losses) ? saved.losses.filter((x) => typeof x === 'number') : [], opening: '' });
    for (const u of saved.moves.slice(0, 600)) {
      if (typeof u !== 'string') return false;
      const m = legalMoves(cur()).find((x) => uciOf(x) === u);
      if (!m) return false;
      applyMove(m);
    }
    const o = detectOpening();
    G.opening = o ? o[1] : '';
    return true;
  }

  /* ================= Event UI ================= */
  /* ---------- Animasi & drag bidak ---------- */
  const reduceMotion = () => { try { return window.matchMedia('(prefers-reduced-motion: reduce)').matches; } catch (e) { return false; } };
  const sqEl = (i) => boardEl.querySelector('.sq[data-sq="' + i + '"]');
  function slide(fromSq, toSq, dur) {
    const fromEl = sqEl(fromSq), toEl = sqEl(toSq);
    const pc = toEl && toEl.querySelector('.pc:not(.ghost)');
    if (!fromEl || !pc || !pc.animate) return;
    const a = fromEl.getBoundingClientRect(), b = toEl.getBoundingClientRect();
    toEl.classList.add('lift');
    const anim = pc.animate([{ transform: 'translate(' + (a.left - b.left) + 'px,' + (a.top - b.top) + 'px)' }, { transform: 'translate(0,0)' }], { duration: dur, easing: 'cubic-bezier(.22,.8,.25,1)' });
    anim.onfinish = anim.oncancel = () => toEl.classList.remove('lift');
  }
  function animateMove(a) {
    if (reduceMotion()) return;
    const dist = Math.hypot((a.from & 7) - (a.to & 7), (a.from >> 3) - (a.to >> 3));
    const dur = Math.round(170 + Math.min(dist, 7) * 22);
    if (a.captured) {
      const capEl = sqEl(a.capSq);
      if (capEl && capEl.animate) {
        const g = el('span', 'pc ghost ' + colorOf(a.captured), GLYPH[a.captured.toLowerCase()] + VS);
        capEl.insertBefore(g, capEl.firstChild);
        const ga = g.animate([{ opacity: 1, transform: 'scale(1)' }, { opacity: 0, transform: 'scale(.6)' }], { duration: dur + 60, delay: dur * 0.55, easing: 'ease-out', fill: 'backwards' });
        ga.onfinish = ga.oncancel = () => g.remove();
      }
    }
    slide(a.from, a.to, dur);
    if (a.rook) slide(a.rook[0], a.rook[1], dur);
  }

  let drag = null, suppressClick = false;
  const canDragFrom = (i) => { const s = cur(), p = s.board[i]; return !G.over && !G.busy && s.turn === G.player && p && colorOf(p) === G.player; };
  boardEl.addEventListener('pointerdown', (e) => {
    if (e.button > 0) return;
    const b = e.target.closest('.sq');
    if (!b) return;
    const i = +b.dataset.sq;
    if (!canDragFrom(i)) return;
    e.preventDefault();
    suppressClick = true;
    const wasSelected = selected === i;
    if (!wasSelected) { selected = i; targets = legalMoves(cur()).filter((x) => x.from === i).map((x) => x.to); render(); }
    const sq = sqEl(i);
    drag = { i, x: e.clientX, y: e.clientY, sq, pc: sq.querySelector('.pc'), moved: false, wasSelected, over: null };
    try { boardEl.setPointerCapture(e.pointerId); } catch (err) { /* abaikan */ }
  });
  boardEl.addEventListener('pointermove', (e) => {
    if (!drag || !drag.pc) return;
    const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
    if (!drag.moved && Math.hypot(dx, dy) < 6) return;
    if (!drag.moved) { drag.moved = true; drag.pc.classList.add('dragging'); drag.sq.classList.add('lift'); }
    drag.pc.style.transform = 'translate(' + dx + 'px,' + dy + 'px) scale(1.12)';
    const under = document.elementFromPoint(e.clientX, e.clientY);
    const t = under && under.closest ? under.closest('.sq') : null;
    if (drag.over && drag.over !== t) drag.over.classList.remove('drop-over');
    drag.over = t && targets.includes(+t.dataset.sq) ? t : null;
    if (drag.over) drag.over.classList.add('drop-over');
  });
  function endDrag(e, cancel) {
    if (!drag) return;
    const d = drag;
    drag = null;
    setTimeout(() => { suppressClick = false; }, 0);
    if (d.over) d.over.classList.remove('drop-over');
    if (!d.moved) {
      if (d.wasSelected) { selected = -1; targets = []; render(); }
      return;
    }
    const under = cancel ? null : document.elementFromPoint(e.clientX, e.clientY);
    const t = under && under.closest ? under.closest('.sq') : null;
    const to = t ? +t.dataset.sq : -1;
    if (to >= 0 && targets.includes(to)) {
      const lm = legalMoves(cur()).filter((x) => x.from === d.i && x.to === to);
      const m = lm.find((x) => x.promo && x.promo.toLowerCase() === 'q') || lm[0];
      if (m) { userMove(m, true); return; }
    }
    if (d.pc.animate && !reduceMotion()) {
      const cur0 = d.pc.style.transform;
      d.pc.classList.remove('dragging');
      d.pc.style.transform = '';
      const back = d.pc.animate([{ transform: cur0 }, { transform: 'translate(0,0) scale(1.1)' }], { duration: 180, easing: 'cubic-bezier(.22,.8,.25,1)' });
      back.onfinish = () => d.sq.classList.remove('lift');
    } else render();
  }
  boardEl.addEventListener('pointerup', (e) => endDrag(e, false));
  boardEl.addEventListener('pointercancel', (e) => endDrag(e, true));
  boardEl.addEventListener('click', (e) => {
    if (suppressClick) { suppressClick = false; return; }
    const b = e.target.closest('.sq');
    if (b) onSquare(+b.dataset.sq);
  });
  window.addEventListener('resize', () => { if (drag) endDrag({ clientX: 0, clientY: 0 }, true); });
  $('#btnNew').addEventListener('click', async () => {
    if (G.moves.length && !G.over) { const ok = await confirmBox('Mulai game baru?', 'Game yang sedang berjalan akan dihapus (tidak dihitung kalah).', 'Mulai baru'); if (!ok) return; }
    newGame(settings.color);
  });
  $('#btnHint').addEventListener('click', showHint);
  $('#btnUndo').addEventListener('click', undo);
  $('#btnFlip').addEventListener('click', () => { flipped = !flipped; render(); if (G.analysis) renderEval(G.analysis.cpWhite, G.analysis.mateWhite); });
  $('#btnResign').addEventListener('click', async () => {
    if (G.over || !G.moves.length) return;
    const ok = await confirmBox('Yakin menyerah?', 'Game ini akan dihitung kalah.', 'Menyerah');
    if (!ok) return;
    G.token++;
    G.busy = false;
    G.over = { over: true, type: 'resign', winner: other(G.player) };
    finishGame();
  });
  $('#btnCopyPgn').addEventListener('click', async () => {
    if (!G.moves.length) { toast('Belum ada langkah untuk disalin.'); return; }
    try { await navigator.clipboard.writeText(pgn()); toast('PGN tersalin ke clipboard ✅'); }
    catch (e) { infoBox('PGN', pgn()); }
  });
  $('#btnResetStats').addEventListener('click', async () => {
    const ok = await confirmBox('Reset statistik?', 'Semua catatan menang, kalah, remis, dan akurasi akan dihapus.', 'Reset');
    if (!ok) return;
    Object.assign(stats, { win: 0, loss: 0, draw: 0, streak: 0, accSum: 0, accN: 0 });
    store.set('cm_stats', stats);
    renderStats();
    toast('Statistik direset.');
  });

  $('#chatForm').addEventListener('submit', (e) => {
    e.preventDefault();
    const input = $('#chatInput');
    const q = clean(input.value, 200);
    input.value = '';
    if (!q) { toast('Tulis pertanyaan dulu ya.'); return; }
    say(q, 'user');
    const a = answer(q);
    if (a) setTimeout(() => say(a), 250);
  });
  $$('.chip').forEach((c) => c.addEventListener('click', () => { const q = c.dataset.ask; say(q, 'user'); const a = answer(q); if (a) setTimeout(() => say(a), 250); }));

  function switchTab(name) {
    $$('.tab').forEach((t) => { const on = t.dataset.tab === name; t.classList.toggle('is-active', on); t.setAttribute('aria-selected', String(on)); });
    $$('.tab-pane').forEach((p) => { p.hidden = p.dataset.pane !== name; });
    if (name === 'stats') renderStats();
  }
  $$('.tab').forEach((t) => t.addEventListener('click', () => switchTab(t.dataset.tab)));
  $$('[data-tab-link]').forEach((a) => a.addEventListener('click', () => switchTab(a.dataset.tabLink)));

  const menuBtn = $('#menuBtn'), mobileNav = $('#mobileNav');
  menuBtn.addEventListener('click', () => { const open = mobileNav.hidden; mobileNav.hidden = !open; menuBtn.setAttribute('aria-expanded', String(open)); });
  mobileNav.addEventListener('click', (e) => { if (e.target.closest('.nav-link')) { mobileNav.hidden = true; menuBtn.setAttribute('aria-expanded', 'false'); } });

  $$('[data-open]').forEach((b) => b.addEventListener('click', () => { if (b.dataset.open === 'dlgSettings') fillSettings(); openDlg(b.dataset.open); }));
  $$('dialog [data-close]').forEach((b) => b.addEventListener('click', () => b.closest('dialog').close()));
  $$('dialog').forEach((d) => d.addEventListener('click', (e) => { if (e.target === d) d.close(); }));

  function fillSettings() {
    $('#setName').value = settings.name;
    $('#setLevel').value = String(settings.level);
    $('#setEngine').value = settings.engine;
    $('#setColor').value = settings.color;
    $('#setCoach').checked = settings.coach;
    $('#setEval').checked = settings.evalBar;
    $('#setHints').checked = settings.hints;
    updateLevelLabel();
  }
  function updateLevelLabel() { const v = +$('#setLevel').value; $('#setLevelVal').textContent = String(v); $('#setLevelName').textContent = LEVEL_NAMES[v - 1]; }
  $('#setLevel').addEventListener('input', updateLevelLabel);
  $('#settingsForm').addEventListener('submit', (e) => {
    e.preventDefault();
    const lv = Math.min(10, Math.max(1, parseInt($('#setLevel').value, 10) || 5));
    const eng = $('#setEngine').value === 'builtin' ? 'builtin' : 'stockfish';
    const colr = ['w', 'b', 'r'].includes($('#setColor').value) ? $('#setColor').value : 'w';
    Object.assign(settings, { name: clean($('#setName').value, 20) || 'Pemain', level: lv, engine: eng, color: colr, coach: $('#setCoach').checked, evalBar: $('#setEval').checked, hints: $('#setHints').checked });
    store.set('cm_settings', settings);
    $('#dlgSettings').close();
    if (eng === 'stockfish' && !sfOk) toast('Stockfish belum aktif, sementara pakai bot bawaan.', true);
    else toast('Pengaturan tersimpan ✅');
    render();
  });

  /* ================= Start ================= */
  renderStats();
  const resumed = restore();
  if (!resumed) newGame(settings.color);
  else { render(); say('Selamat datang kembali, ' + (settings.name || 'Pemain') + '! Game terakhirmu aku lanjutkan.'); }
  initStockfish().then((ok) => {
    sfOk = ok;
    if (ok) { SF.w.postMessage('isready'); setEngineStatus('Stockfish 10 siap · offline', 'ok'); }
    else setEngineStatus(location.protocol === 'file:' ? 'Bot bawaan aktif · buka lewat server/Vercel untuk Stockfish' : 'Bot bawaan aktif (Stockfish tidak termuat)', 'warn');
    renderPlayers();
    if (resumed) afterTurnChange();
    else if (!G.busy && cur().turn === G.player) requestAnalysis(false);
  });
})();
