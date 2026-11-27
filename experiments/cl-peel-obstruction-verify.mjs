// Independent verification of the 4-generation CL / IterPeel sublinear obstruction families.
// Uses experiments/shared/check.mjs (with transpose, since check.mjs follows arcs toward Q).
import assert from 'node:assert/strict';
import { isQuasiKernel, transpose } from './shared/check.mjs';

function makeRng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s + 0x6D2B79F5) >>> 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function createBitGraph(n) {
  const words = (n + 31) >>> 5;
  return { n, words, outBits: new Uint32Array(n * words), inBits: new Uint32Array(n * words) };
}
function setArc(g, u, v) {
  if (u === v) return;
  g.outBits[u * g.words + (v >>> 5)] |= (1 << (v & 31));
  g.inBits[v * g.words + (u >>> 5)] |= (1 << (u & 31));
}
function hasArc(g, u, v) {
  return (g.outBits[u * g.words + (v >>> 5)] & (1 << (v & 31))) !== 0;
}
function bitToAdj(g) {
  const out = Array.from({ length: g.n }, () => []);
  for (let u = 0; u < g.n; u++) {
    for (let v = 0; v < g.n; v++) if (hasArc(g, u, v)) out[u].push(v);
  }
  return out;
}
function assertTournament(g) {
  for (let u = 0; u < g.n; u++) {
    for (let v = u + 1; v < g.n; v++) {
      const uv = hasArc(g, u, v), vu = hasArc(g, v, u);
      assert.equal(uv !== vu, true, `Pair (${u},${v}) not tournament edge`);
    }
  }
}

// Forward+backward CL on bit-packed graph. mode: 'maxOut' | 'unif' | 'invIn' | 'weightedDyn'
function runCLBit(g, f, mode, allowed, rng) {
  const n = g.n, words = g.words, outBits = g.outBits, inBits = g.inBits;
  const alive = new Uint8Array(n);
  const active = [];
  for (let i = 0; i < n; i++) {
    if (!allowed || allowed[i]) { alive[i] = 1; active.push(i); }
  }
  const ws = new Float64Array(n);
  const S = [];
  while (active.length > 0) {
    const len = active.length;
    let chosenIdx = len - 1;
    if (mode === 'maxOut') {
      let best = -1;
      for (let i = 0; i < len; i++) {
        const v = active[i], base = v * words;
        let deg = 0;
        for (let j = 0; j < len; j++) {
          const u = active[j];
          if (outBits[base + (u >>> 5)] & (1 << (u & 31))) deg++;
        }
        if (deg > best) { best = deg; chosenIdx = i; }
      }
    } else if (mode === 'unif') {
      chosenIdx = (rng() * len) | 0;
    } else {
      let totalW = 0;
      for (let i = 0; i < len; i++) {
        const v = active[i], base = v * words;
        let w = 1;
        if (mode === 'weightedDyn') {
          let fOut = f[v];
          for (let j = 0; j < len; j++) {
            const u = active[j];
            if (outBits[base + (u >>> 5)] & (1 << (u & 31))) fOut += f[u];
          }
          w = f[v] / fOut;
        } else if (mode === 'invIn') {
          let inDeg = 0;
          for (let j = 0; j < len; j++) {
            const u = active[j];
            if (inBits[base + (u >>> 5)] & (1 << (u & 31))) inDeg++;
          }
          w = 1 / (inDeg + 1);
        }
        ws[i] = w;
        totalW += w;
      }
      let r = rng() * totalW;
      for (let i = 0; i < len; i++) { r -= ws[i]; if (r <= 0) { chosenIdx = i; break; } }
    }
    const chosen = active[chosenIdx];
    S.push(chosen);
    alive[chosen] = 0;
    const base = chosen * words;
    let write = 0;
    for (let i = 0; i < len; i++) {
      const u = active[i];
      if (u === chosen || (outBits[base + (u >>> 5)] & (1 << (u & 31)))) alive[u] = 0;
      else active[write++] = u;
    }
    active.length = write;
  }
  const dom = new Uint8Array(n);
  const K = [];
  for (let i = S.length - 1; i >= 0; i--) {
    const v = S[i];
    if (dom[v]) continue;
    K.push(v); dom[v] = 1;
    const base = v * words;
    for (let u = 0; u < n; u++) if (outBits[base + (u >>> 5)] & (1 << (u & 31))) dom[u] = 1;
  }
  return K;
}

function extendMISAndEval(g, f, Kinit) {
  const n = g.n, words = g.words, outBits = g.outBits, inBits = g.inBits;
  const dom = new Uint8Array(n), into = new Uint8Array(n);
  const K = Kinit.slice();
  const mark = (v) => {
    dom[v] = 1;
    const base = v * words;
    for (let u = 0; u < n; u++) {
      if (outBits[base + (u >>> 5)] & (1 << (u & 31))) dom[u] = 1;
      if (inBits[base + (u >>> 5)] & (1 << (u & 31))) into[u] = 1;
    }
  };
  for (const v of K) mark(v);
  for (let v = 0; v < n; v++) {
    if (!dom[v] && !into[v]) { K.push(v); mark(v); }
  }
  let fDom = 0;
  for (let i = 0; i < n; i++) if (dom[i]) fDom += f[i];
  return { K, fDom };
}

function runIterPeelBit(g, f, mode, rng) {
  const n = g.n, words = g.words, outBits = g.outBits;
  const rem = new Uint8Array(n).fill(1);
  let remCnt = n;
  const layers = [];
  while (remCnt > 0) {
    const K = runCLBit(g, f, mode, rem, rng);
    layers.push(K);
    for (const u of K) {
      if (rem[u]) { rem[u] = 0; remCnt--; }
      const base = u * words;
      for (let v = 0; v < n; v++) {
        if (rem[v] && (outBits[base + (v >>> 5)] & (1 << (v & 31)))) { rem[v] = 0; remCnt--; }
      }
    }
  }
  let bestF = 0, bestQ = null;
  for (let i = 0; i < layers.length; i++) {
    const dom = new Uint8Array(n), Q = [];
    const addQ = (u) => {
      Q.push(u); dom[u] = 1;
      const base = u * words;
      for (let v = 0; v < n; v++) if (outBits[base + (v >>> 5)] & (1 << (v & 31))) dom[v] = 1;
    };
    for (const u of layers[i]) addQ(u);
    for (let j = i - 1; j >= 0; j--) {
      for (const u of layers[j]) if (!dom[u]) addQ(u);
    }
    const ext = extendMISAndEval(g, f, Q);
    if (ext.fDom > bestF) { bestF = ext.fDom; bestQ = ext.K; }
  }
  return { K: bestQ, fDom: bestF, numLayers: layers.length };
}

// --- Graph Builders ---
function buildGStair(L, t) {
  const n = L * (t + 1);
  const g = createBitGraph(n);
  const aOf = (l) => l * (t + 1), bOf = (l, x) => l * (t + 1) + 1 + x;
  for (let l = 0; l < L; l++) {
    for (let x = 0; x < t; x++) setArc(g, aOf(l), bOf(l, x));
    for (let q = l + 1; q < L; q++) {
      setArc(g, aOf(q), aOf(l));
      for (let x = 0; x < t; x++) {
        setArc(g, bOf(l, x), aOf(q));
        setArc(g, bOf(q, x), aOf(l));
        for (let y = 0; y < t; y++) setArc(g, bOf(l, x), bOf(q, y));
      }
    }
  }
  return { g, f: new Float64Array(n).fill(1) };
}

function buildAsymTrap(s, t, m, r, rng) {
  const n = s + t + m;
  const g = createBitGraph(n);
  for (let a = 0; a < s; a++) for (let b = 0; b < t; b++) setArc(g, a, s + b);
  for (let b = 0; b < t; b++) for (let c = 0; c < m; c++) setArc(g, s + b, s + t + c);
  const mark = new Int32Array(s);
  for (let c = 0; c < m; c++) {
    let picked = 0;
    while (picked < r) {
      const a = (rng() * s) | 0;
      if (mark[a] !== c + 1) { mark[a] = c + 1; setArc(g, s + t + c, a); picked++; }
    }
  }
  return { g, f: new Float64Array(n).fill(1) };
}

function buildPortal(M, t) {
  const n = M + M * t;
  const g = createBitGraph(n);
  for (let i = 0; i < M; i++) {
    for (let j = i + 1; j < M; j++) {
      if ((i + j) & 1) setArc(g, i, j); else setArc(g, j, i);
    }
    const bi0 = M + i * t;
    for (let x = 0; x < t; x++) setArc(g, i, bi0 + x);
    for (let j = 0; j < M; j++) {
      if (j === i) continue;
      const bj0 = M + j * t;
      for (let x = 0; x < t; x++) {
        setArc(g, bi0 + x, j);
        for (let y = 0; y < t; y++) setArc(g, bi0 + x, bj0 + y);
      }
    }
  }
  return { g, f: new Float64Array(n).fill(1) };
}

function buildBackupTournPortal(M, L, rng) {
  const n = M + M * L;
  const g = createBitGraph(n);
  const f = new Float64Array(n);
  const W = M * L * 1000;
  for (let j = 0; j < M; j++) {
    f[j] = W;
    for (let j2 = 0; j2 < M; j2++) {
      if (j2 === j) continue;
      setArc(g, j, j2);
      const base = M + j2 * L;
      for (let r = 0; r < L; r++) setArc(g, j, base + r);
    }
  }
  for (let j = 0; j < M; j++) {
    const base = M + j * L;
    for (let r = 0; r < L; r++) {
      const u = base + r;
      f[u] = 1;
      setArc(g, u, j);
      for (let r2 = 0; r2 < L; r2++) if (r2 !== r) setArc(g, u, base + r2);
    }
  }
  for (let j1 = 0; j1 < M; j1++) {
    const b1 = M + j1 * L;
    for (let j2 = j1 + 1; j2 < M; j2++) {
      const b2 = M + j2 * L;
      for (let r1 = 0; r1 < L; r1++) {
        for (let r2 = 0; r2 < L; r2++) {
          if (rng() < 0.5) setArc(g, b1 + r1, b2 + r2); else setArc(g, b2 + r2, b1 + r1);
        }
      }
    }
  }
  return { g, f };
}

function buildOrientedBackupPortal(p, rMax, L, allChains, rng) {
  const qr = new Set();
  for (let x = 1; x < p; x++) qr.add((x * x) % p);
  const beats = Array.from({ length: p }, () => new Uint8Array(p));
  for (let i = 0; i < p; i++) {
    for (let j = 0; j < p; j++) if (i !== j && qr.has((j - i + p) % p)) beats[i][j] = 1;
  }
  const chains = [];
  const isDom = (arr) => {
    const cov = new Uint8Array(p);
    for (const u of arr) { cov[u] = 1; for (let v = 0; v < p; v++) if (beats[u][v]) cov[v] = 1; }
    for (let v = 0; v < p; v++) if (!cov[v]) return false;
    return true;
  };
  const dfs = (chain) => {
    if (allChains ? chain.length >= 1 : (chain.length >= 2 && isDom(chain))) chains.push(chain.slice());
    if (chain.length === rMax) return;
    for (let v = 0; v < p; v++) {
      if (chain.every((u) => beats[v][u])) { chain.push(v); dfs(chain); chain.pop(); }
    }
  };
  for (let v = 0; v < p; v++) dfs([v]);

  const nA = chains.length * L, n = p + nA;
  const g = createBitGraph(n);
  const f = new Float64Array(n);
  const delta = 1 / (nA * p * 1000);
  for (let i = 0; i < p; i++) {
    f[i] = 1;
    for (let j = 0; j < p; j++) if (beats[i][j]) setArc(g, i, j);
  }
  for (let idx = 0; idx < chains.length; idx++) {
    const X = new Set(chains[idx]);
    for (let r = 0; r < L; r++) {
      const u = p + idx * L + r;
      f[u] = delta;
      for (let b = 0; b < p; b++) { if (X.has(b)) setArc(g, u, b); else setArc(g, b, u); }
    }
  }
  for (let i = 0; i < nA; i++) {
    for (let j = i + 1; j < nA; j++) {
      if (rng() < 0.5) setArc(g, p + i, p + j); else setArc(g, p + j, p + i);
    }
  }
  assertTournament(g);
  return { g, f };
}

const rng = makeRng(20261207);

console.log('[1] Gen 1: G_stair(16, 16) vs IterPeel(MaxOut)');
{
  const { g, f } = buildGStair(16, 16);
  const r = runIterPeelBit(g, f, 'maxOut', rng);
  assert.ok(isQuasiKernel(transpose(bitToAdj(g)), r.K), 'G_stair QK invalid');
  const ratio = r.fDom / g.n;
  console.log(`  G_stair(16,16, n=${g.n}): IterPeel(MaxOut)+MIS = ${ratio.toFixed(4)} (expected 32/272 = 0.1176)`);
  assert.ok(ratio < 0.15);
}

console.log('[2] Gen 2: AsymTrap vs Unif+MIS, Dyn-1/(in+1)+MIS, and WeightedDyn+MIS');
{
  const { g, f } = buildAsymTrap(22, 220, 1200, 8, rng);
  let sUnif = 0, sIn = 0, sDyn = 0;
  const trials = 25;
  for (let t = 0; t < trials; t++) {
    sUnif += extendMISAndEval(g, f, runCLBit(g, f, 'unif', null, rng)).fDom / g.n;
    sIn += extendMISAndEval(g, f, runCLBit(g, f, 'invIn', null, rng)).fDom / g.n;
    sDyn += extendMISAndEval(g, f, runCLBit(g, f, 'weightedDyn', null, rng)).fDom / g.n;
  }
  console.log(`  AsymTrap(n=${g.n}): Unif+MIS=${(sUnif/trials).toFixed(4)}, 1/(in+1)+MIS=${(sIn/trials).toFixed(4)}, WeightedDyn+MIS=${(sDyn/trials).toFixed(4)}`);
  assert.ok(sIn / trials < 0.25 && sDyn / trials > 0.90);
}

console.log('[3] Gen 3: Bidirected Portal(12, 144) vs Single WeightedDyn+MIS');
{
  const { g, f } = buildPortal(12, 144);
  let sSingle = 0;
  const trials = 20;
  for (let t = 0; t < trials; t++) {
    sSingle += extendMISAndEval(g, f, runCLBit(g, f, 'weightedDyn', null, rng)).fDom / g.n;
  }
  console.log(`  Portal(12,144, n=${g.n}): Single WeightedDyn+MIS = ${(sSingle/trials).toFixed(4)}`);
  assert.ok(sSingle / trials < 0.25);
}

console.log('[4] Gen 4 (General): BackupTournamentPortal(M=5, 6) vs IterPeel(WeightedDyn)+MIS');
for (const [M, L] of [[5, 160], [6, 300]]) {
  const { g, f } = buildBackupTournPortal(M, L, rng);
  const fTot = f.reduce((a, b) => a + b, 0);
  let sum = 0, fullM = 0;
  const trials = 10;
  for (let t = 0; t < trials; t++) {
    const r = runIterPeelBit(g, f, 'weightedDyn', rng);
    if (t === 0 && g.n <= 900) assert.ok(isQuasiKernel(transpose(bitToAdj(g)), r.K), 'BackupTourn QK invalid');
    sum += r.fDom / fTot;
    if (r.numLayers === M) fullM++;
  }
  console.log(`  BackupTournPortal(M=${M}, L=${L}, n=${g.n}): IterPeel+MIS = ${(sum/trials).toFixed(4)} (1/M=${(1/M).toFixed(4)}, fullM=${fullM}/${trials})`);
  assert.ok(sum / trials < (1 / M) + 0.02);
}

console.log('[5] Gen 3 & 4 (Pure Tournament!): BackupPowerSetPortal(QR_7, QR_11) vs Single & IterPeel');
for (const [p, rMax, L, allChains] of [[7, 3, 20, true], [11, 4, 14, false]]) {
  const { g, f } = buildOrientedBackupPortal(p, rMax, L, allChains, rng);
  const fTot = f.reduce((a, b) => a + b, 0);
  let sS = 0, sP = 0;
  const trials = 20;
  for (let t = 0; t < trials; t++) {
    const rS = extendMISAndEval(g, f, runCLBit(g, f, 'weightedDyn', null, rng));
    const rP = runIterPeelBit(g, f, 'weightedDyn', rng);
    if (t === 0 && g.n <= 1100) {
      const rev = transpose(bitToAdj(g));
      assert.ok(isQuasiKernel(rev, rS.K) && isQuasiKernel(rev, rP.K), 'QR portal QK invalid');
    }
    sS += rS.fDom / fTot;
    sP += rP.fDom / fTot;
  }
  console.log(`  QR_${p} Tournament(L=${L}, n=${g.n}): Single+MIS=${(sS/trials).toFixed(4)}, IterPeel+MIS=${(sP/trials).toFixed(4)}`);
  assert.ok(sS / trials < 0.46 && sP / trials < 0.48);
}

console.log('ALL CL/ITERPEEL OBSTRUCTION VERIFICATIONS PASSED.');
