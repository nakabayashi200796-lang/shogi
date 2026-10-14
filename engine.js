/* 将棋の頭脳（ルールとAI）
   盤は 11列×13行 の一列の数の並びで持つ（まわりは「壁」。桂馬が飛び出しても壁に当たるよう上下は2行ずつ）。
   中のマスの番号は (段+2)*11 + (列+1)。段0が上（一段目）、列0が左（9筋）。先手が下から攻める向き。
   画面からは普通の script として読み込み、AIの読みは同じファイルを Worker（裏で動く別の作業員）として動かす */
'use strict';
(function () {

const W = 11, NSQ = W * 13;
const WALL = 32, GOTE = 16, PROMO = 1 << 16;
const FU = 1, KY = 2, KE = 3, GI = 4, KI = 5, KA = 6, HI = 7, OU = 8, UM = 14, RY = 15;
const RANK = new Int8Array(NSQ).fill(-1), FILE = new Int8Array(NSQ).fill(-1);
const SQ = new Uint8Array(81);                       // 画面のマス番号（段*9+列）→ 中の番号
const UI = new Int16Array(NSQ).fill(-1);             // 中の番号 → 画面のマス番号
for (let r = 0; r < 9; r++) for (let f = 0; f < 9; f++) {
  const s = (r + 2) * W + f + 1;
  SQ[r * 9 + f] = s; UI[s] = r * 9 + f; RANK[s] = r; FILE[s] = f;
}

/* ---------- 駒の動き（先手から見た向き） ---------- */
const N = -W, S = W, E = 1, Wt = -1, NE = -W + 1, NW = -W - 1, SE = W + 1, SW = W - 1;
const DIR8 = [N, S, E, Wt, NE, NW, SE, SW];
const GOLD = [N, NE, NW, E, Wt, S];
const DEF = {
  1: { s: [N] }, 2: { l: [N] }, 3: { s: [2 * N + Wt, 2 * N + E] }, 4: { s: [N, NE, NW, SE, SW] }, 5: { s: GOLD },
  6: { l: [NE, NW, SE, SW] }, 7: { l: [N, S, E, Wt] }, 8: { s: DIR8 },
  9: { s: GOLD }, 10: { s: GOLD }, 11: { s: GOLD }, 12: { s: GOLD },
  14: { s: [N, S, E, Wt], l: [NE, NW, SE, SW] }, 15: { s: [NE, NW, SE, SW], l: [N, S, E, Wt] },
};
const STEP = [], SLIDE = [];
const ATK = new Uint8Array(32 * 64);                // ATK[駒*64 + 向き+32]：1=1マス動ける 2=走れる
for (let pc = 0; pc < 32; pc++) { STEP[pc] = []; SLIDE[pc] = []; }
for (const t in DEF) {
  for (const g of [0, 1]) {
    const pc = +t | (g ? GOTE : 0), sg = g ? -1 : 1;
    STEP[pc] = (DEF[t].s || []).map(d => d * sg);
    SLIDE[pc] = (DEF[t].l || []).map(d => d * sg);
    for (const d of STEP[pc]) ATK[pc * 64 + d + 32] |= 1;
    for (const d of SLIDE[pc]) ATK[pc * 64 + d + 32] |= 3;
  }
}
const KNIGHT_FROM = [[-(2 * N + Wt), -(2 * N + E)], [2 * N + Wt, 2 * N + E]];  // 桂がいる場所＝マス − 桂の動き

/* ---------- 駒の値打ち（歩＝100） ---------- */
const VAL = [0, 100, 270, 300, 420, 510, 650, 740, 0, 540, 500, 520, 510, 0, 950, 1080];
const HVAL = [0, 115, 300, 330, 470, 560, 720, 840];  // 持ち駒は好きな所に打てるぶん少し高い

/* ---------- 局面 ---------- */
const board = new Uint8Array(NSQ);
const hand = new Uint8Array(16);                     // hand[手番*8 + 駒]
const kingSq = new Int32Array(2);
let side = 0, mat = 0, h1 = 0, h2 = 0;

// 局面の指紋（同じ局面を見分ける乱数の組）
let seed = 0x9e3779b9 | 0;
function rnd() { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return seed | 0; }
const Z1 = new Int32Array(32 * NSQ), Z2 = new Int32Array(32 * NSQ);
const HZ1 = new Int32Array(16 * 20), HZ2 = new Int32Array(16 * 20);
for (let i = 0; i < Z1.length; i++) { Z1[i] = rnd(); Z2[i] = rnd(); }
for (let i = 0; i < HZ1.length; i++) { HZ1[i] = rnd(); HZ2[i] = rnd(); }
const ZS1 = rnd(), ZS2 = rnd();

function clearBoard() {
  board.fill(WALL);
  for (let i = 0; i < 81; i++) board[SQ[i]] = 0;
  hand.fill(0); kingSq[0] = kingSq[1] = 0; side = 0;
}
function rehash() {
  h1 = 0; h2 = 0; mat = 0;
  for (let i = 0; i < 81; i++) {
    const s = SQ[i], p = board[s]; if (!p) continue;
    h1 ^= Z1[p * NSQ + s]; h2 ^= Z2[p * NSQ + s];
    mat += (p & GOTE ? -1 : 1) * VAL[p & 15];
    if ((p & 15) === OU) kingSq[p & GOTE ? 1 : 0] = s;
  }
  for (let hi = 0; hi < 16; hi++) {
    const c = hand[hi]; if (!c) continue;
    h1 ^= HZ1[hi * 20 + c] ^ HZ1[hi * 20]; h2 ^= HZ2[hi * 20 + c] ^ HZ2[hi * 20];
    mat += (hi >= 8 ? -1 : 1) * HVAL[hi & 7] * c;
  }
  if (side) { h1 ^= ZS1; h2 ^= ZS2; }
}

/* ---------- 手の形：to | from<<8 | 成り<<16 | 打つ駒<<17（打つときは from=0） ---------- */
const MAXPLY = 128, MSTRIDE = 700;
const MV = new Int32Array(MAXPLY * MSTRIDE), MSC = new Int32Array(MAXPLY * MSTRIDE);
const U_m = new Int32Array(1024), U_cap = new Uint8Array(1024), U_h1 = new Int32Array(1024), U_h2 = new Int32Array(1024), U_mat = new Int32Array(1024);
let sp = 0;

// mode 0：AI用（歩・角・飛の「成れるのに成らない」手は省く） 1：全部 2：駒を取る手だけ
function gen(n, mode) {
  const us = side, g = us << 4;
  for (let i = 0; i < 81; i++) {
    const s = SQ[i], p = board[s];
    if (p === 0 || (p & GOTE) !== g) continue;
    const t = p & 15;
    const st = STEP[p];
    for (let k = 0; k < st.length; k++) {
      const to = s + st[k], q = board[to];
      if (q === WALL || (q !== 0 && (q & GOTE) === g)) continue;
      if (mode === 2 && q === 0) continue;
      n = addMove(n, s, to, t, us, mode);
    }
    const sl = SLIDE[p];
    for (let k = 0; k < sl.length; k++) {
      const d = sl[k];
      for (let to = s + d; ; to += d) {
        const q = board[to];
        if (q === WALL) break;
        if (q !== 0) { if ((q & GOTE) !== g) n = addMove(n, s, to, t, us, mode); break; }
        if (mode !== 2) n = addMove(n, s, to, t, us, mode);
      }
    }
  }
  if (mode === 2) return n;
  const hb = us * 8;
  let pawnFiles = 0;
  if (hand[hb + FU]) {
    for (let i = 0; i < 81; i++) { const p = board[SQ[i]]; if (p === (FU | g)) pawnFiles |= 1 << (i % 9); }
  }
  for (let t = 1; t <= 7; t++) {
    if (!hand[hb + t]) continue;
    for (let i = 0; i < 81; i++) {
      const s = SQ[i];
      if (board[s]) continue;
      const rr = us ? 8 - RANK[s] : RANK[s];
      if (rr === 0 && (t === FU || t === KY)) continue;
      if (rr <= 1 && t === KE) continue;
      if (t === FU && (pawnFiles >> FILE[s]) & 1) continue;
      MV[n++] = s | (t << 17);
    }
  }
  return n;
}
function addMove(n, s, to, t, us, mode) {
  if (t <= 7 && t !== KI) {
    const rt = us ? 8 - RANK[to] : RANK[to], rf = us ? 8 - RANK[s] : RANK[s];
    if (rt <= 2 || rf <= 2) {
      MV[n++] = to | (s << 8) | PROMO;
      if ((t === FU || t === KY) && rt === 0) return n;
      if (t === KE && rt <= 1) return n;
      if (mode !== 1 && (t === FU || t === KA || t === HI)) return n;
    }
  }
  MV[n++] = to | (s << 8);
  return n;
}

function make(m) {
  const to = m & 255, from = (m >>> 8) & 255, us = side, sg = us ? -1 : 1;
  U_m[sp] = m; U_h1[sp] = h1; U_h2[sp] = h2; U_mat[sp] = mat;
  let cap = 0;
  if (from === 0) {
    const t = (m >>> 17) & 15, pc = t | (us << 4), hi = us * 8 + t, c = hand[hi];
    h1 ^= HZ1[hi * 20 + c] ^ HZ1[hi * 20 + c - 1]; h2 ^= HZ2[hi * 20 + c] ^ HZ2[hi * 20 + c - 1];
    hand[hi] = c - 1;
    board[to] = pc; h1 ^= Z1[pc * NSQ + to]; h2 ^= Z2[pc * NSQ + to];
    mat += sg * (VAL[t] - HVAL[t]);
  } else {
    let pc = board[from];
    cap = board[to];
    h1 ^= Z1[pc * NSQ + from]; h2 ^= Z2[pc * NSQ + from];
    board[from] = 0;
    if (cap) {
      h1 ^= Z1[cap * NSQ + to]; h2 ^= Z2[cap * NSQ + to];
      const bt = cap & 7, hi = us * 8 + bt, c = hand[hi];
      h1 ^= HZ1[hi * 20 + c] ^ HZ1[hi * 20 + c + 1]; h2 ^= HZ2[hi * 20 + c] ^ HZ2[hi * 20 + c + 1];
      hand[hi] = c + 1;
      mat += sg * (VAL[cap & 15] + HVAL[bt]);
    }
    if (m & PROMO) { mat += sg * (VAL[(pc & 15) + 8] - VAL[pc & 15]); pc += 8; }
    board[to] = pc; h1 ^= Z1[pc * NSQ + to]; h2 ^= Z2[pc * NSQ + to];
    if ((pc & 15) === OU) kingSq[us] = to;
  }
  U_cap[sp++] = cap;
  side ^= 1; h1 ^= ZS1; h2 ^= ZS2;
  if (NN) nnRecord(m, cap);
}
function unmake() {
  sp--;
  const m = U_m[sp];
  side ^= 1; h1 = U_h1[sp]; h2 = U_h2[sp]; mat = U_mat[sp];
  if (m === 0) return;                              // パス（AIの読みの中だけで使う）
  const to = m & 255, from = (m >>> 8) & 255, us = side;
  if (from === 0) { board[to] = 0; hand[us * 8 + ((m >>> 17) & 15)]++; return; }
  let pc = board[to];
  if (m & PROMO) pc -= 8;
  board[from] = pc;
  const cap = U_cap[sp];
  board[to] = cap;
  if (cap) hand[us * 8 + (cap & 7)]--;
  if ((pc & 15) === OU) kingSq[us] = from;
}
function makeNull() { U_m[sp] = 0; U_h1[sp] = h1; U_h2[sp] = h2; U_mat[sp] = mat; U_cap[sp++] = 0; side ^= 1; h1 ^= ZS1; h2 ^= ZS2; if (NN) { DN[sp] = 0; DK[sp] = 0; AV[sp * 2] = AV[sp * 2 + 1] = 0; } }

// マス s に、by 側の駒が利いているか
function attacked(s, by) {
  const g = by << 4;
  for (let k = 0; k < 8; k++) {
    const d = DIR8[k];
    let q = s - d, p = board[q];
    if (p !== 0) {
      if (p !== WALL && (p & GOTE) === g && ATK[p * 64 + d + 32]) return true;
      continue;
    }
    q -= d;
    while ((p = board[q]) === 0) q -= d;
    if (p !== WALL && (p & GOTE) === g && (ATK[p * 64 + d + 32] & 2)) return true;
  }
  const kf = KNIGHT_FROM[by];
  if (board[s + kf[0]] === (KE | g) || board[s + kf[1]] === (KE | g)) return true;
  return false;
}
function inCheck() { const k = kingSq[side]; return k ? attacked(k, side ^ 1) : false; }
// 直前の手で、指した側の玉が取られる形になっていないか（make の直後に呼ぶ）
function leftInCheck() { const k = kingSq[side ^ 1]; return k ? attacked(k, side) : false; }

// 打ち歩詰め：歩を打って王手をかけ、相手が逃げられないなら反則（make の直後に呼ぶ）
function pawnDropCheck(m) {
  if ((m >>> 8) & 255 || ((m >>> 17) & 15) !== FU) return false;
  const k = kingSq[side];
  return k !== 0 && (m & 255) === k + (side ? W : -W);
}
function hasLegal(ply) {
  const b = ply * MSTRIDE, e = gen(b, 0);
  for (let i = b; i < e; i++) {
    make(MV[i]);
    const bad = leftInCheck();
    unmake();
    if (!bad) return true;
  }
  return false;
}
function illegalAfterMake(m, ply) {
  if (leftInCheck()) return true;
  if (pawnDropCheck(m) && !hasLegal(ply + 1)) return true;
  return false;
}

/* ---------- 盤の見立て ---------- */
// 相手の玉に近いほど、攻めの駒は値打ちが上がる。自分の玉の近くの金銀は守りとして上がる
const ATT_S = [0, 55, 35, 15, 5, 0, 0, 0, 0, 0];
const ATT_B = [0, 70, 55, 35, 18, 8, 0, 0, 0, 0];
const DEF_G = [0, 45, 28, 8, 0, 0, 0, 0, 0, 0];
const KROW = [-70, -60, -50, -40, -30, -20, 0, 18, 25];   // 玉の段（先手から見て、下の段ほど安全）
let matOnly = false;

/* ---------- 学習済みの見立て（新しい神だけが使う。中身は eval.bin、src	rain	rain.py が作る） ----------
   手番側と相手側の目線で「自分の玉の位置 × 駒の種類と場所・持ち駒の枚数」の印を集め、小さな NNUE で点数にする。
   印の番号の付け方は train.py の feats() とまったく同じにすること */
let nnOn = false, NN = null;
const TI = [0, 0, 1, 2, 3, 4, 5, 6, -1, 7, 8, 9, 10, 0, 11, 12];   // 駒の種類 → 0〜12（成り駒は7〜12）
const HOFF = [0, 0, 18, 22, 26, 30, 34, 36];                      // 持ち駒の印の始まり（歩〜飛）
function loadNN(buf) {
  const dv = new DataView(buf);
  if (dv.getUint32(0, true) !== 0x4e4e4853) throw new Error('eval.bin の形がちがう');
  const H = dv.getInt32(4, true), H2 = dv.getInt32(8, true), NPc = dv.getInt32(12, true), NK = dv.getInt32(16, true);
  const Q = dv.getFloat32(20, true), SCALE = dv.getFloat32(24, true);
  let o = 28;
  const nW1 = NK * NPc * H;
  const q = new Int16Array(buf.slice(o, o + nW1 * 2)); o += nW1 * 2;
  const W1 = new Float32Array(nW1);
  for (let i = 0; i < nW1; i++) W1[i] = q[i] / Q;
  const f32 = (n) => { const a = new Float32Array(buf.slice(o, o + n * 4)); o += n * 4; return a; };
  const B1 = f32(H), W2 = f32(2 * H * H2), B2 = f32(H2), W3 = f32(H2), B3 = f32(1);
  NN = { H, H2, NP: NPc, SCALE, W1, B1, W2, B2, W3, B3: B3[0], acc: new Float32Array(2 * H), z: new Float32Array(H2) };
  ACC = new Float32Array(1100 * 2 * H); AV.fill(0);
}
// P の目線の第1層を acc[off..off+H) に作る
function nnAcc(P, acc, off) {
  const { H, NP: NPc, W1, B1 } = NN;
  for (let j = 0; j < H; j++) acc[off + j] = B1[j];
  const ks = kingSq[P];
  let kr = ks ? RANK[ks] : 8, kf = ks ? FILE[ks] : 4;
  if (P) { kr = 8 - kr; kf = 8 - kf; }
  const mir = kf > 4;
  if (mir) kf = 8 - kf;
  const base = (kr * 5 + kf) * NPc;
  const add = (pid) => { const w = (base + pid) * H; for (let j = 0; j < H; j++) acc[off + j] += W1[w + j]; };
  for (let i = 0; i < 81; i++) {
    const s = SQ[i], p = board[s];
    if (!p) continue;
    const t = p & 15, o = (p & GOTE) ? 1 : 0, rel = P ? 1 - o : o;
    let r = RANK[s], f = FILE[s];
    if (P) { r = 8 - r; f = 8 - f; }
    if (mir) f = 8 - f;
    if (t === OU) { if (rel === 1) add(2106 + r * 9 + f); continue; }
    add((rel * 13 + TI[t]) * 81 + r * 9 + f);
  }
  for (let o = 0; o < 2; o++) {
    const rel = P ? 1 - o : o;
    for (let t = 1; t <= 7; t++) {
      const n = hand[o * 8 + t];
      for (let c = 0; c < n; c++) add(2187 + rel * 38 + HOFF[t] + c);
    }
  }
}
/* 速くするしかけ：局面ごと（sp の深さごと）に第1層の結果を取っておき、1手で変わった駒の分だけ足し引きする。
   変化は make のときに「盤のマスの駒が消えた・現れた」「持ち駒の何枚目が増えた・減った」の形で書き残す。
   自分の玉が動いたら目線の基準が変わるので、その目線だけ全部数え直す */
const DMAX = 6;
const DN = new Uint8Array(1100), DK = new Uint8Array(1100), DE = new Int32Array(1100 * DMAX), DS = new Int8Array(1100 * DMAX);
const AV = new Uint8Array(1100 * 2);
let ACC = null;
function nnRecord(m, cap) {
  const L = sp, us = side ^ 1, to = m & 255, from = (m >>> 8) & 255, k = L * DMAX;
  let n = 0;
  const put = (e, sg) => { DE[k + n] = e; DS[k + n] = sg; n++; };
  DK[L] = 0;
  if (!from) {
    const t = (m >>> 17) & 15;
    put((1 << 20) | (us << 16) | (t << 8) | hand[us * 8 + t], -1);     // 打ったあとの枚数＝消えた印の番号
    put((to << 8) | board[to], 1);
  } else {
    const pcNew = board[to], pcOld = (m & PROMO) ? pcNew - 8 : pcNew;
    put((from << 8) | pcOld, -1);
    if (cap) { put((to << 8) | cap, -1); const bt = cap & 7; put((1 << 20) | (us << 16) | (bt << 8) | (hand[us * 8 + bt] - 1), 1); }
    put((to << 8) | pcNew, 1);
    if ((pcOld & 15) === OU) DK[L] = 1 << us;
  }
  DN[L] = n;
  AV[L * 2] = AV[L * 2 + 1] = 0;
}
function nnPid(P, e, mir) {
  if (e & (1 << 20)) {
    const o = (e >> 16) & 1, t = (e >> 8) & 15, idx = e & 255, rel = P ? 1 - o : o;
    return 2187 + rel * 38 + HOFF[t] + idx;
  }
  const s = e >> 8, p = e & 255, t = p & 15, o = (p & GOTE) ? 1 : 0, rel = P ? 1 - o : o;
  let r = RANK[s], f = FILE[s];
  if (P) { r = 8 - r; f = 8 - f; }
  if (mir) f = 8 - f;
  if (t === OU) return rel === 1 ? 2106 + r * 9 + f : -1;
  return (rel * 13 + TI[t]) * 81 + r * 9 + f;
}
function nnEnsure(P) {
  const { H, NP: NPc, W1 } = NN, L = sp;
  if (AV[L * 2 + P]) return;
  let k = L;
  while (k > 0 && !AV[k * 2 + P] && !(DK[k] & (1 << P))) k--;
  if (!AV[k * 2 + P]) { nnAcc(P, ACC, (L * 2 + P) * H); AV[L * 2 + P] = 1; return; }
  // k は数えてある局面。k+1〜L の変化を順に足し引きする（その間に自分の玉は動いていない）
  const ks = kingSq[P];
  let kr = ks ? RANK[ks] : 8, kf = ks ? FILE[ks] : 4;
  if (P) { kr = 8 - kr; kf = 8 - kf; }
  const mir = kf > 4;
  if (mir) kf = 8 - kf;
  const base = (kr * 5 + kf) * NPc;
  for (let j = k + 1; j <= L; j++) {
    const src = ((j - 1) * 2 + P) * H, dst = (j * 2 + P) * H;
    ACC.copyWithin(dst, src, src + H);
    for (let q = 0; q < DN[j]; q++) {
      const pid = nnPid(P, DE[j * DMAX + q], mir);
      if (pid < 0) continue;
      const w = (base + pid) * H;
      if (DS[j * DMAX + q] > 0) for (let i = 0; i < H; i++) ACC[dst + i] += W1[w + i];
      else for (let i = 0; i < H; i++) ACC[dst + i] -= W1[w + i];
    }
    AV[j * 2 + P] = 1;
  }
}
function nnEval() {
  const { H, H2, W2, B2, W3, acc, z } = NN;
  nnEnsure(side); nnEnsure(side ^ 1);
  const a0 = (sp * 2 + side) * H, a1 = (sp * 2 + (side ^ 1)) * H;
  for (let j = 0; j < H; j++) { acc[j] = ACC[a0 + j]; acc[H + j] = ACC[a1 + j]; }
  for (let k = 0; k < H2; k++) z[k] = B2[k];
  for (let i = 0; i < 2 * H; i++) {
    let a = acc[i];
    if (a <= 0) continue;
    if (a > 1) a = 1;
    const row = i * H2;
    for (let k = 0; k < H2; k++) z[k] += a * W2[row + k];
  }
  let y = NN.B3;
  for (let k = 0; k < H2; k++) { let c = z[k]; if (c <= 0) continue; if (c > 1) c = 1; y += c * W3[k]; }
  return Math.round(y * NN.SCALE);
}

function evaluate() {
  if (nnOn) return nnEval();
  if (matOnly) return side ? -mat : mat;
  let sc = mat;
  const k0 = kingSq[0], k1 = kingSq[1];
  const r0 = k0 ? RANK[k0] : 8, f0 = k0 ? FILE[k0] : 4, r1 = k1 ? RANK[k1] : 0, f1 = k1 ? FILE[k1] : 4;
  let big = 0;
  for (let i = 0; i < 81; i++) {
    const s = SQ[i], p = board[s];
    if (!p) continue;
    const t = p & 15;
    if (t === OU) continue;
    const r = RANK[s], f = FILE[s];
    const gote = p & GOTE;
    if (t === HI || t === KA || t === RY || t === UM) big++;
    // 攻め：相手玉との距離 / 守り：自玉との距離
    const ex = gote ? Math.max(Math.abs(r - r0), Math.abs(f - f0)) : Math.max(Math.abs(r - r1), Math.abs(f - f1));
    const ow = gote ? Math.max(Math.abs(r - r1), Math.abs(f - f1)) : Math.max(Math.abs(r - r0), Math.abs(f - f0));
    let v = 0;
    if (t === FU) v = ow <= 1 ? 12 : 0;
    else if (t === HI || t === KA || t === RY || t === UM) {
      v = ATT_B[ex];
      // 大駒は動ける広さも値打ち
      const sl = SLIDE[p];
      let mob = 0;
      for (let k = 0; k < sl.length; k++) { const d = sl[k]; let q = s + d; while (board[q] === 0) { mob++; q += d; } if (board[q] !== WALL && (board[q] & GOTE) !== gote) mob++; }
      v += mob * 3;
    } else {
      v = ATT_S[ex];
      if (t === KI || t === GI || t >= 9) v += DEF_G[ow];
    }
    sc += gote ? -v : v;
  }
  // 中盤までは玉が下の段・端寄りにいるほうが安全
  if (big >= 2) {
    sc += KROW[r0] - KROW[8 - r1];
    sc += (f0 === 4 ? -20 : 0) - (f1 === 4 ? -20 : 0);
  }
  return (side ? -sc : sc) + 20;
}

/* ---------- 読み ---------- */
const MATE = 30000, INF = 32000, NONE = -99999;
const ABORT = { abort: true };
let nodes = 0, deadline = Infinity, rootBest = 0;
const TBITS = 20, TSIZE = 1 << TBITS, TMASK = TSIZE - 1;
const TK = new Int32Array(TSIZE), TV = new Int16Array(TSIZE), TD = new Int8Array(TSIZE), TF = new Uint8Array(TSIZE), TM = new Int32Array(TSIZE);
function ttClear() { TK.fill(0); TD.fill(-1); TM.fill(0); }
ttClear();
const KILL1 = new Int32Array(MAXPLY), KILL2 = new Int32Array(MAXPLY);
const HIST = new Int32Array(32 * NSQ);

// 対局の流れ（千日手を見分けるため）。HS:局面の指紋 HCK:その局面で王手がかかっているか HNL:パスで来た局面
const HLEN = 2048;
const HS1 = new Int32Array(HLEN), HS2 = new Int32Array(HLEN), HCK = new Uint8Array(HLEN), HNL = new Uint8Array(HLEN);
let base = 0;                                         // いまの局面が対局の何番目か

function repetition(n) {
  if (HNL[n] || HNL[n - 1]) return NONE;
  for (let i = n - 2; i >= 0 && n - i <= 80; i -= 2) {
    if (HNL[i] || HNL[i + 1]) return NONE;
    if (i <= n - 4 && HS1[i] === h1 && HS2[i] === h2) {
      let xAll = true, yAll = true;
      for (let j = i + 2; j <= n; j += 2) if (!HCK[j]) { xAll = false; break; }
      for (let j = i + 1; j < n; j += 2) if (!HCK[j]) { yAll = false; break; }
      if (xAll) return 3000;     // ずっと王手をかけられていた＝相手の連続王手の千日手で、こちらの勝ち
      if (yAll) return -3000;
      return 0;
    }
  }
  return NONE;
}

function scoreMoves(b, e, ttMove, ply) {
  for (let i = b; i < e; i++) {
    const m = MV[i];
    if (m === ttMove) { MSC[i] = 1 << 30; continue; }
    const to = m & 255, from = (m >>> 8) & 255;
    let sc = 0;
    if (from) {
      const cap = board[to], pc = board[from];
      if (cap) sc = 200000 + VAL[cap & 15] * 16 - VAL[pc & 15];
      if (m & PROMO) sc += 150000;
      if (!sc) {
        if (m === KILL1[ply]) sc = 120000; else if (m === KILL2[ply]) sc = 110000;
        else sc = HIST[pc * NSQ + to];
      }
    } else {
      const t = (m >>> 17) & 15;
      if (m === KILL1[ply]) sc = 120000; else if (m === KILL2[ply]) sc = 110000;
      else sc = HIST[(t | (side << 4)) * NSQ + to] - 50;
    }
    MSC[i] = sc;
  }
}
function pickNext(i, e) {
  let bi = i, bs = MSC[i];
  for (let j = i + 1; j < e; j++) if (MSC[j] > bs) { bs = MSC[j]; bi = j; }
  if (bi !== i) { const m = MV[i]; MV[i] = MV[bi]; MV[bi] = m; const s = MSC[i]; MSC[i] = MSC[bi]; MSC[bi] = s; }
  return MV[i];
}

function qsearch(alpha, beta, ply, qd) {
  if ((++nodes & 1023) === 0 && Date.now() > deadline) throw ABORT;
  const chk = inCheck();
  const b = ply * MSTRIDE;
  if (chk && qd < 3) {
    const e = gen(b, 0);
    scoreMoves(b, e, 0, ply);
    let best = -INF, legal = 0;
    for (let i = b; i < e; i++) {
      const m = pickNext(i, e);
      make(m);
      if (illegalAfterMake(m, ply)) { unmake(); continue; }
      legal++;
      const v = -qsearch(-beta, -alpha, ply + 1, qd + 1);
      unmake();
      if (v > best) { best = v; if (v > alpha) { alpha = v; if (v >= beta) return v; } }
    }
    return legal ? best : -MATE + ply;
  }
  const stand = evaluate();
  if (stand >= beta) return stand;
  if (stand > alpha) alpha = stand;
  if (qd >= 8 || ply >= MAXPLY - 4) return stand;
  const e = gen(b, 2);
  scoreMoves(b, e, 0, ply);
  let best = stand;
  for (let i = b; i < e; i++) {
    const m = pickNext(i, e);
    const cap = board[m & 255];
    if (stand + VAL[cap & 15] + HVAL[cap & 7] + 250 < alpha && !(m & PROMO)) continue;
    make(m);
    if (leftInCheck()) { unmake(); continue; }
    const v = -qsearch(-beta, -alpha, ply + 1, qd + 1);
    unmake();
    if (v > best) { best = v; if (v > alpha) { alpha = v; if (v >= beta) return v; } }
  }
  return best;
}

let extLimit = 20;
function search(depth, alpha, beta, ply, canNull) {
  const n = base + ply;
  HS1[n] = h1; HS2[n] = h2; HNL[n] = (!canNull && ply > 0) ? 1 : 0;
  const chk = inCheck();
  HCK[n] = chk ? 1 : 0;
  if (ply > 0) { const r = repetition(n); if (r !== NONE) return r; }
  if ((++nodes & 1023) === 0 && Date.now() > deadline) throw ABORT;
  if (ply >= MAXPLY - 10) return evaluate();
  if (chk && ply < extLimit) depth++;
  if (depth <= 0) return qsearch(alpha, beta, ply, 0);

  // 置換表（前に読んだ局面の控え）
  const ti = h1 & TMASK;
  let ttMove = 0;
  if (TK[ti] === h2) {
    ttMove = TM[ti];
    if (ply > 0 && TD[ti] >= depth) {
      let v = TV[ti];
      if (v > MATE - 500) v -= ply; else if (v < -MATE + 500) v += ply;
      const f = TF[ti];
      if (f === 0 || (f === 1 && v >= beta) || (f === 2 && v <= alpha)) return v;
    }
  }
  const pv = beta - alpha > 1;
  let stat = 0;
  if (!chk) {
    stat = evaluate();
    if (!pv && ply > 0) {
      if (depth <= 3 && stat - 160 * depth >= beta && beta < MATE - 500) return stat;
      if (canNull && depth >= 3 && stat >= beta) {
        makeNull();
        let v;
        try { v = -search(depth - 1 - (depth >= 7 ? 3 : 2), -beta, -beta + 1, ply + 1, false); }
        finally { unmake(); }
        if (v >= beta) return v >= MATE - 500 ? beta : v;
      }
    }
  }
  const b = ply * MSTRIDE, e = gen(b, 0);
  scoreMoves(b, e, ttMove, ply);
  let best = -INF, bestMove = 0, legal = 0;
  const a0 = alpha;
  for (let i = b; i < e; i++) {
    const m = pickNext(i, e);
    const to = m & 255, from = (m >>> 8) & 255;
    const quiet = !(from && board[to]) && !(m & PROMO);
    const mover = from ? board[from] : (((m >>> 17) & 15) | (side << 4));
    make(m);
    if (illegalAfterMake(m, ply)) { unmake(); continue; }
    legal++;
    const gives = inCheck();
    // 浅いところで、明らかに足りない静かな手は読まない
    if (quiet && !chk && !gives && !pv && depth <= 2 && legal > 1 && stat + 120 + 180 * depth <= alpha) { unmake(); continue; }
    let v;
    try {
      if (legal === 1) v = -search(depth - 1, -beta, -alpha, ply + 1, true);
      else {
        let red = 0;
        if (depth >= 3 && quiet && !chk && !gives && legal > 3 && m !== KILL1[ply] && m !== KILL2[ply]) red = legal > 10 ? 2 : 1;
        if (red && pv) red--;
        v = -search(depth - 1 - red, -alpha - 1, -alpha, ply + 1, true);
        if (v > alpha && (red || v < beta)) v = -search(depth - 1, -beta, -alpha, ply + 1, true);
      }
    } finally { unmake(); }
    if (v > best) {
      best = v; bestMove = m;
      if (ply === 0) rootBest = m;
      if (v > alpha) {
        alpha = v;
        if (v >= beta) {
          if (quiet) {
            if (KILL1[ply] !== m) { KILL2[ply] = KILL1[ply]; KILL1[ply] = m; }
            const hx = mover * NSQ + to; HIST[hx] += depth * depth; if (HIST[hx] > 100000) for (let k = 0; k < HIST.length; k++) HIST[k] >>= 1;
          }
          break;
        }
      }
    }
  }
  if (!legal) return -MATE + ply;
  let sv = best;
  if (sv > MATE - 500) sv += ply; else if (sv < -MATE + 500) sv -= ply;
  if (sv > 32000) sv = 32000; if (sv < -32000) sv = -32000;
  if (TD[ti] <= depth || TK[ti] !== h2) {
    TK[ti] = h2; TV[ti] = sv; TD[ti] = depth; TM[ti] = bestMove;
    TF[ti] = best >= beta ? 1 : best <= a0 ? 2 : 0;
  }
  return best;
}

/* ---------- 詰みの読み（王手だけを続けて玉を詰ませる） ---------- */
let mateMove = 0, mateNodes = 0, mateLimit = 0;
function mateOr(n, ply) {
  if ((++mateNodes & 255) === 0 && (Date.now() > deadline || mateNodes > mateLimit)) throw ABORT;
  const b = ply * MSTRIDE, e = gen(b, 0);
  for (let i = b; i < e; i++) {
    const m = MV[i];
    make(m);
    if (leftInCheck() || !inCheck()) { unmake(); continue; }
    if (pawnDropCheck(m) && !hasLegal(ply + 1)) { unmake(); continue; }
    let ok;
    try { ok = mateAnd(n - 1, ply + 1); } finally { unmake(); }
    if (ok) { if (ply === 0) mateMove = m; return true; }
  }
  return false;
}
function mateAnd(k, ply) {
  const b = ply * MSTRIDE, e = gen(b, 0);
  let legal = 0;
  for (let i = b; i < e; i++) {
    const m = MV[i];
    make(m);
    if (illegalAfterMake(m, ply)) { unmake(); continue; }
    legal++;
    if (k === 0) { unmake(); return false; }
    let ok;
    try { ok = mateOr(k - 1, ply + 1); } finally { unmake(); }
    if (!ok) return false;
  }
  return true;
}
// n手以内の詰みがあればその初手を返す（無ければ 0）
function findMate(maxPly, ms, nodeLimit) {
  const saveDl = deadline;
  spRoot = sp;
  deadline = Date.now() + ms; mateNodes = 0; mateLimit = nodeLimit || 3e6;
  let found = 0;
  try {
    for (let n = 1; n <= maxPly; n += 2) { mateMove = 0; if (mateOr(n, 0)) { found = mateMove; break; } }
  } catch (e) { if (e !== ABORT) throw e; while (sp > spRoot) unmake(); }
  deadline = saveDl;
  return found;
}

/* ---------- 強さの段 ---------- */
const LEVELS = [null,
  { random: true },
  { depth: 1, noise: 160, matOnly: true },
  { depth: 2, noise: 70 },
  { depth: 3, time: 1500 },
  { depth: 5, time: 900, mate: 3 },
  { depth: 7, time: 2000, mate: 5 },
  { depth: 40, time: 4000, mate: 7 },
  { depth: 40, time: 5000, mate: 7, nn: true },
];

let spRoot = 0;
function legalList(mode) {
  const b = (MAXPLY - 2) * MSTRIDE, e = gen(b, mode), out = [];
  for (let i = b; i < e; i++) {
    const m = MV[i];
    make(m);
    const bad = illegalAfterMake(m, MAXPLY - 4);
    unmake();
    if (!bad) out.push(m);
  }
  return out;
}

function iterate(maxDepth, ms) {
  deadline = Date.now() + ms;
  spRoot = sp; nodes = 0;
  let best = 0, value = 0, depth = 0;
  for (let d = 1; d <= maxDepth; d++) {
    rootBest = 0;
    try {
      extLimit = d * 2 + 4;
      const v = search(d, -INF, INF, 0, false);
      best = rootBest; value = v; depth = d;
      if (Math.abs(v) > MATE - 200) break;
    } catch (e) {
      if (e !== ABORT) throw e;
      while (sp > spRoot) unmake();
      if (rootBest && d > 1) best = rootBest;
      break;
    }
  }
  deadline = Infinity;
  return { move: best, value, depth };
}

function useNN(on) {
  on = !!on && !!NN;
  if (on !== nnOn) { nnOn = on; ttClear(); }
}
function think(level) {
  const L = LEVELS[level] || LEVELS[7];
  useNN(L.nn);
  const list = legalList(0);
  if (!list.length) return { move: 0, value: -MATE };
  if (L.random) return { move: list[Math.floor(Math.random() * list.length)], value: 0 };
  spRoot = sp;
  for (let i = 0; i < MAXPLY; i++) { KILL1[i] = KILL2[i] = 0; }
  HIST.fill(0);
  if (L.mate) {
    const m = findMate(L.mate, L.time * 0.3, 2e6);
    if (m) return { move: m, value: MATE - 1, mate: true };
  }
  if (L.noise) {
    // 全部の手をきっちり読んで点数をつけ、そこに揺らぎを足して選ぶ（弱い段らしい迷い）
    matOnly = !!L.matOnly;
    let bestV = -INF, best = list[0];
    const scores = [];
    for (const m of list) {
      make(m);
      base++;
      let v;
      try { v = -search(L.depth - 1, -INF, INF, 0, true); } finally { base--; unmake(); }
      scores.push(v);
      const nv = v + (Math.random() * 2 - 1) * L.noise;
      if (nv > bestV) { bestV = nv; best = m; }
    }
    matOnly = false;
    return { move: best, value: scores[list.indexOf(best)] };
  }
  return iterate(L.depth, L.time);
}

// 振り返り用：この局面の形勢（手番側から見た点）と、AIのおすすめ
function analyze(ms) {
  useNN(true);
  const list = legalList(0);
  if (!list.length) return { value: -MATE, best: 0 };
  const r = iterate(7, ms);
  return { value: r.value, best: r.move || list[0] };
}

/* ---------- 局面の出し入れ（画面から使う） ---------- */
const START_SFEN = 'lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1';
const LETTER = { p: FU, l: KY, n: KE, s: GI, g: KI, b: KA, r: HI, k: OU };
const LETTERS = ' PLNSGBRK';

function loadSFEN(sfen) {
  clearBoard(); sp = 0;
  const [bd, sd, hd] = sfen.trim().split(/\s+/);
  const rows = bd.split('/');
  for (let r = 0; r < 9; r++) {
    let f = 0, promo = false;
    for (const ch of rows[r]) {
      if (ch === '+') { promo = true; continue; }
      if (/[0-9]/.test(ch)) { f += +ch; continue; }
      const t = LETTER[ch.toLowerCase()];
      board[SQ[r * 9 + f]] = (t + (promo ? 8 : 0)) | (ch === ch.toLowerCase() ? GOTE : 0);
      f++; promo = false;
    }
  }
  side = sd === 'w' ? 1 : 0;
  if (hd && hd !== '-') {
    let num = 0;
    for (const ch of hd) {
      if (/[0-9]/.test(ch)) { num = num * 10 + (+ch); continue; }
      const t = LETTER[ch.toLowerCase()];
      hand[(ch === ch.toLowerCase() ? 8 : 0) + t] += num || 1;
      num = 0;
    }
  }
  rehash();
  AV.fill(0);
  base = 0; record();
}
// いまの局面を対局の流れに書き足す
function record() { HS1[base] = h1; HS2[base] = h2; HCK[base] = inCheck() ? 1 : 0; HNL[base] = 0; }

const FILES = 'abcdefghi';
function sqName(s) { return (9 - FILE[s]) + FILES[RANK[s]]; }
function toUSI(m) {
  const to = m & 255, from = (m >>> 8) & 255;
  if (!from) return LETTERS[(m >>> 17) & 15] + '*' + sqName(to);
  return sqName(from) + sqName(to) + (m & PROMO ? '+' : '');
}
function parseSq(s) { const f = 9 - (+s[0]), r = FILES.indexOf(s[1]); return SQ[r * 9 + f]; }
function fromUSI(u) {
  if (u[1] === '*') return parseSq(u.slice(2, 4)) | (LETTERS.indexOf(u[0]) << 17);
  return parseSq(u.slice(2, 4)) | (parseSq(u.slice(0, 2)) << 8) | (u[4] === '+' ? PROMO : 0);
}

// 最初から手を並べ直す
function setup(moves, sfen) {
  loadSFEN(sfen || START_SFEN);
  for (const u of moves) playUSI(u);
}
function playUSI(u) {
  const m = fromUSI(u);
  const cap = (m >>> 8) & 255 ? board[m & 255] : 0;
  make(m);
  sp = 0;                                           // 対局の手は戻さないので積まない
  AV[0] = AV[1] = 0;
  base++; record();
  return { capture: cap ? cap & 15 : 0, check: HCK[base] === 1 };
}

// 千日手・詰みなど、対局の終わりを見る。{ over, winner(0先手 1後手 -1引き分け), why }
function status(maxMoves) {
  const legal = legalList(1).length;
  if (!legal) return { over: true, winner: side ^ 1, why: '詰み' };
  // 同じ局面が4回目
  let cnt = 1, first = base;
  for (let i = base - 2; i >= 0; i -= 2) if (HS1[i] === h1 && HS2[i] === h2) { cnt++; first = i; }
  if (cnt >= 4) {
    let xAll = true, yAll = true;
    for (let j = first + 2; j <= base; j += 2) if (!HCK[j]) { xAll = false; break; }
    for (let j = first + 1; j < base; j += 2) if (!HCK[j]) { yAll = false; break; }
    if (xAll) return { over: true, winner: side, why: '連続王手の千日手' };
    if (yAll) return { over: true, winner: side ^ 1, why: '連続王手の千日手' };
    return { over: true, winner: -1, why: '千日手' };
  }
  if (maxMoves && base >= maxMoves) return { over: true, winner: -1, why: '手数の上限' };
  return { over: false, check: HCK[base] === 1 };
}

// いまの局面を SFEN の文字に（学習用のデータ作りで使う）
const SF = ' plnsgbrk', SFP = { 9: '+p', 10: '+l', 11: '+n', 12: '+s', 14: '+b', 15: '+r' };
function sfen() {
  const rows = [];
  for (let r = 0; r < 9; r++) {
    let row = '', e = 0;
    for (let f = 0; f < 9; f++) {
      const p = board[SQ[r * 9 + f]];
      if (!p) { e++; continue; }
      if (e) { row += e; e = 0; }
      const t = p & 15, ch = t >= 9 ? SFP[t] : SF[t];
      row += p & GOTE ? ch : ch.toUpperCase();
    }
    if (e) row += e;
    rows.push(row);
  }
  let hs = '';
  for (const s of [0, 1]) for (const t of [7, 6, 5, 4, 3, 2, 1]) {
    const n = hand[s * 8 + t]; if (!n) continue;
    hs += (n > 1 ? n : '') + (s ? SF[t] : SF[t].toUpperCase());
  }
  return rows.join('/') + ' ' + (side ? 'w' : 'b') + ' ' + (hs || '-') + ' 1';
}
// 画面に描くための局面。b[段*9+列] = 駒（0なし。先手1〜15、後手は+16）、hand[0|1][駒1〜7]
function view() {
  const b = new Array(81);
  for (let i = 0; i < 81; i++) b[i] = board[SQ[i]];
  return { b, hand: [Array.from(hand.slice(0, 8)), Array.from(hand.slice(8, 16))], side, ply: base };
}
// 指せる手を画面の言葉で
function legalMoves() {
  return legalList(1).map(m => {
    const to = m & 255, from = (m >>> 8) & 255;
    return { usi: toUSI(m), from: from ? UI[from] : -1, to: UI[to], drop: from ? 0 : (m >>> 17) & 15, promo: !!(m & PROMO) };
  });
}
function decode(u) {
  const m = fromUSI(u), to = m & 255, from = (m >>> 8) & 255;
  return { from: from ? UI[from] : -1, to: UI[to], drop: from ? 0 : (m >>> 17) & 15, promo: !!(m & PROMO) };
}

// 棋譜の書き方（▲７六歩 など）。指す前の局面で呼ぶ
const ZEN = '０１２３４５６７８９', KAN = '〇一二三四五六七八九';
const KNAME = ['', '歩', '香', '桂', '銀', '金', '角', '飛', '玉', 'と', '成香', '成桂', '成銀', '', '馬', '龍'];
function kifu(u, prevTo) {
  const m = fromUSI(u), to = m & 255, from = (m >>> 8) & 255;
  const mark = side ? '△' : '▲';
  const place = (prevTo !== undefined && prevTo !== null && prevTo >= 0 && UI[to] === prevTo) ? '同' : ZEN[9 - FILE[to]] + KAN[RANK[to] + 1];
  if (!from) return mark + place + KNAME[(m >>> 17) & 15] + '打';
  const t = board[from] & 15;
  let s = mark + place + KNAME[t];
  if (m & PROMO) s += '成';
  else if (t <= 7 && t !== KI) {
    const us = side, rt = us ? 8 - RANK[to] : RANK[to], rf = us ? 8 - RANK[from] : RANK[from];
    if (rt <= 2 || rf <= 2) s += '不成';
  }
  return s;
}

// 詰みの確かめ（講座で使う）。手番側が n 手以内に詰ませられるなら初手の USI
function mateIn(n, ms) { const m = findMate(n, ms || 3000, 5e6); return m ? toUSI(m) : ''; }
// この局面で手番側が詰んでいるか
function isMated() { return legalList(1).length === 0; }

const Engine = {
  START_SFEN, LEVELS, VAL, KNAME,
  loadSFEN, sfen, setup, playUSI, status, view, legalMoves, decode, kifu, mateIn, isMated, inCheck: () => inCheck(),
  think: (level) => { const r = think(level); return { move: r.move ? toUSI(r.move) : '', value: r.value, depth: r.depth || 0, mate: !!r.mate }; },
  analyze: (ms) => { const r = analyze(ms); return { value: r.value, best: r.best ? toUSI(r.best) : '' }; },
  // 検品用
  loadNN, hasNN: () => !!NN, _nnEval: () => { const o = nnOn; nnOn = true; const v = evaluate(); nnOn = o; return v; }, _evaluate: () => evaluate(), _nnFull: () => { const sv = AV.slice(); AV.fill(0); const v = nnEval(); AV.set(sv); return v; }, _mv: (i) => MV[i], _legalInts: () => legalList(1), _unmakeAll: () => { while (sp > 0) unmake(); },
  _perft: perft, _gen: gen, _make: make, _unmake: unmake, _hash: () => [h1, h2], _sideToMove: () => side, ttClear,
  get nodes() { return nodes; },
};
function perft(d, ply) {
  ply = ply || 0;
  const b = ply * MSTRIDE, e = gen(b, 1);
  let c = 0;
  for (let i = b; i < e; i++) {
    const m = MV[i];
    make(m);
    if (!illegalAfterMake(m, ply)) c += d <= 1 ? 1 : perft(d - 1, ply + 1);
    unmake();
  }
  return c;
}

/* ---------- Worker として動いているときの受け口 ---------- */
if (typeof WorkerGlobalScope !== 'undefined' && self instanceof WorkerGlobalScope) {
  // 学習済みの見立ては大きい（数MB）ので、必要になったときに1回だけ読み込む
  let nnTry = null;
  const ensureNN = () => {
    if (NN) return Promise.resolve();
    if (!nnTry) nnTry = fetch('eval.bin').then(r => { if (!r.ok) throw new Error(r.status); return r.arrayBuffer(); }).then(loadNN).catch(() => {});
    return nnTry;
  };
  let queue = Promise.resolve();
  self.onmessage = (ev) => { queue = queue.then(() => handle(ev.data)); };
  const handle = async (m) => {
    if ((m.cmd === 'think' && LEVELS[m.level] && LEVELS[m.level].nn) || m.cmd === 'analyze') await ensureNN();
    if (m.cmd === 'think') {
      setup(m.moves, m.sfen);
      self.postMessage({ id: m.id, cmd: 'think', result: Engine.think(m.level) });
    } else if (m.cmd === 'analyze') {
      // 手の並びの、それぞれの手を指す直前の局面（と最後の局面）を読む
      const out = [];
      setup([], m.sfen);
      ttClear();
      for (let i = 0; i <= m.moves.length; i++) {
        out.push(Engine.analyze(m.ms || 300));
        self.postMessage({ id: m.id, cmd: 'progress', done: i + 1, total: m.moves.length + 1 });
        if (i < m.moves.length) playUSI(m.moves[i]);
      }
      self.postMessage({ id: m.id, cmd: 'analyze', result: out });
    } else if (m.cmd === 'mate') {
      setup(m.moves || [], m.sfen);
      self.postMessage({ id: m.id, cmd: 'mate', result: mateIn(m.n, m.ms) });
    }
  };
} else if (typeof module !== 'undefined') {
  module.exports = Engine;
} else {
  self.Engine = Engine;
}
})();
