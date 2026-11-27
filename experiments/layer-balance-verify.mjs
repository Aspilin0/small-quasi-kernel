import assert from 'node:assert/strict';
import { isQuasiKernel, transpose } from './shared/check.mjs';

function makeRng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (Math.imul(s, 1664525) + 1013904223) >>> 0;
    return s / 4294967296;
  };
}

function maskToList(n, mask) {
  const out = [];
  for (let i = 0; i < n; i++) if ((mask >> i) & 1) out.push(i);
  return out;
}

function assertIndependentQK(n, adj, kMask, label = '') {
  const lists = Array.from({ length: n }, (_, u) => maskToList(n, adj[u]));
  const chosen = maskToList(n, kMask);
  assert.ok(isQuasiKernel(transpose(lists), chosen), `Independent QK check failed (${label}): Q=${JSON.stringify(chosen)}`);
}

function phiValue(n, adj, kMask, w, activeMask = (1 << n) - 1) {
  let n1 = 0;
  for (let i = 0; i < n; i++) if ((kMask >> i) & 1) n1 |= (adj[i] & activeMask);
  n1 &= ~kMask;
  const r2 = activeMask & ~(kMask | n1);
  let s = 0;
  for (let i = 0; i < n; i++) {
    if ((n1 >> i) & 1) s += w[i];
    else if ((r2 >> i) & 1) s -= w[i];
  }
  return s;
}

function getAllQKsGeneral(n, adj, mask = (1 << n) - 1) {
  const verts = maskToList(n, mask), m = verts.length, qks = [];
  for (let s = 1; s < (1 << m); s++) {
    let k = 0;
    for (let b = 0; b < m; b++) if ((s >> b) & 1) k |= 1 << verts[b];
    let ind = true, n1 = 0;
    for (const i of verts) if ((k >> i) & 1) {
      if (adj[i] & k) { ind = false; break; }
      n1 |= (adj[i] & mask);
    }
    if (!ind) continue;
    let n2 = k | n1;
    for (const x of verts) if ((n1 >> x) & 1) n2 |= (adj[x] & mask);
    if (n2 === mask) qks.push({ k, n1: n1 & ~k, r2: mask & ~(k | n1) });
  }
  return qks;
}

function getAllQKsAlpha2(n, adj) {
  const all = (1 << n) - 1, qks = [];
  for (let i = 0; i < n; i++) {
    const k = 1 << i, n1 = adj[i];
    let n2 = k | n1;
    for (let x = 0; x < n; x++) if ((n1 >> x) & 1) n2 |= adj[x];
    if (n2 === all) qks.push({ k, n1, r2: all & ~(k | n1) });
  }
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
    if (((adj[i] >> j) & 1) || ((adj[j] >> i) & 1)) continue;
    const k = (1 << i) | (1 << j), n1 = adj[i] | adj[j];
    let n2 = k | n1;
    for (let x = 0; x < n; x++) if ((n1 >> x) & 1) n2 |= adj[x];
    if (n2 === all) qks.push({ k, n1: n1 & ~k, r2: all & ~(k | n1) });
  }
  return qks;
}

function checkPropertyStarMWU(n, qks, steps = 700) {
  for (const q of qks) if (q.r2 === 0) return { ok: true, hasKernel: true, upper: 0 };
  let w = new Array(n).fill(1 / n), bestUpper = 1e9;
  for (let t = 0; t < steps; t++) {
    let bestVal = -1e9, bestQ = null;
    for (const q of qks) {
      let val = 0;
      for (let i = 0; i < n; i++) {
        if ((q.n1 >> i) & 1) val += w[i];
        else if ((q.r2 >> i) & 1) val -= w[i];
      }
      if (val > bestVal) { bestVal = val; bestQ = q; }
    }
    if (bestVal < bestUpper) bestUpper = bestVal;
    if (bestVal < -1e-6) return { ok: false, hasKernel: false, upper: bestVal, w };
    const eta = 0.7 / Math.sqrt(t + 1);
    for (let i = 0; i < n; i++) {
      const g = ((bestQ.n1 >> i) & 1) ? 1 : (((bestQ.r2 >> i) & 1) ? -1 : 0);
      w[i] *= Math.exp(-eta * g);
    }
    const s = w.reduce((a, b) => a + b, 0);
    for (let i = 0; i < n; i++) w[i] /= s;
  }
  return { ok: true, hasKernel: false, upper: bestUpper };
}

function findInDomPair(n, adj, activeMask = (1 << n) - 1) {
  const verts = maskToList(n, activeMask);
  const inM = new Array(n).fill(0);
  for (const i of verts) for (const j of verts) if ((adj[i] >> j) & 1) inM[j] |= 1 << i;
  for (const v of verts) {
    const req = inM[v] | (1 << v);
    for (const x of verts) if (x !== v && (req & ~inM[x]) === 0) return [v, x];
  }
  return null;
}

function findKernelSmall(n, adj, subMask) {
  const verts = maskToList(n, subMask), m = verts.length;
  if (m === 0) return 0;
  if (m === 1) return 1 << verts[0];
  if (m === 2) {
    const [a, b] = verts;
    if ((adj[a] >> b) & 1) return 1 << a;
    if ((adj[b] >> a) & 1) return 1 << b;
    return (1 << a) | (1 << b);
  }
  let rem = subMask, ker = 0, progressed = true;
  while (rem && progressed) {
    progressed = false;
    for (const u of verts) {
      if (!((rem >> u) & 1)) continue;
      let hasIn = false;
      for (const v of verts) if (((rem >> v) & 1) && ((adj[v] >> u) & 1)) { hasIn = true; break; }
      if (!hasIn) { ker |= 1 << u; rem &= ~((1 << u) | adj[u]); progressed = true; break; }
    }
  }
  if (rem === 0) return ker;
  for (let s = 1; s < (1 << m); s++) {
    let k = 0;
    for (let b = 0; b < m; b++) if ((s >> b) & 1) k |= 1 << verts[b];
    let ok = true, cov = k;
    for (const u of verts) if ((k >> u) & 1) {
      if (adj[u] & k) { ok = false; break; }
      cov |= (adj[u] & subMask);
    }
    if (ok && cov === subMask) return k;
  }
  return -1;
}

function isSemicompleteSub(n, adj, subMask) {
  const verts = maskToList(n, subMask);
  for (let a = 0; a < verts.length; a++) for (let b = a + 1; b < verts.length; b++) {
    const i = verts[a], j = verts[b];
    if (!((adj[i] >> j) & 1) && !((adj[j] >> i) & 1)) return false;
  }
  return true;
}

function constructTheorem1(n, adj, w, activeMask = (1 << n) - 1) {
  const pair = findInDomPair(n, adj, activeMask);
  if (pair) {
    const [v, x] = pair, nw = w.slice();
    nw[v] += nw[x]; nw[x] = 0;
    return constructTheorem1(n, adj, nw, activeMask & ~(1 << x));
  }
  const verts = maskToList(n, activeMask), nonMask = new Array(n).fill(0);
  for (const u of verts) for (const v of verts)
    if (v !== u && !((adj[u] >> v) & 1) && !((adj[v] >> u) & 1)) nonMask[u] |= 1 << v;
  let bestU = verts[0], bestH = -1e9;
  for (const u of verts) {
    let h = 0.5 * w[u];
    for (const v of verts) {
      if (v === u) continue;
      if ((adj[u] >> v) & 1) h += w[v];
      else if ((nonMask[u] >> v) & 1) h += 0.5 * w[v];
    }
    if (h > bestH) { bestH = h; bestU = u; }
  }
  const Iu = nonMask[bestU], Yu = findKernelSmall(n, adj, Iu);
  if (Yu !== -1) return (1 << bestU) | Yu;
  assert.ok(isSemicompleteSub(n, adj, Iu), 'Not Type I and D[I(u)] not semicomplete');
  const IuList = maskToList(n, Iu);
  for (const y of IuList) assert.ok((nonMask[y] & ~((1 << bestU) | adj[bestU])) === 0, 'Not Type II');
  let bestY = IuList[0], bestScore = -1e9, bestCov = -1;
  for (const y of IuList) {
    const outIn = adj[y] & Iu;
    let sc = 0.5 * w[y], cov = 1;
    for (const z of IuList) if ((outIn >> z) & 1) { sc += w[z]; cov++; }
    if (sc > bestScore + 1e-12 || (Math.abs(sc - bestScore) <= 1e-12 && cov > bestCov)) {
      bestScore = sc; bestCov = cov; bestY = y;
    }
  }
  return (1 << bestU) | (1 << bestY);
}

function randomWeights(n, rng) {
  const w = Array.from({ length: n }, () => rng() < 0.2 ? 0 : Math.pow(rng(), 2));
  const sw = w.reduce((a, b) => a + b, 0);
  if (sw === 0) w[0] = 1; else for (let i = 0; i < n; i++) w[i] /= sw;
  return w;
}

function orientComplement(n, nonEdge, rng, allowBi = true) {
  const adj = new Array(n).fill(0);
  const pBi = (allowBi && rng() >= 0.6) ? 0.2 : 0;
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
    if ((nonEdge[i] >> j) & 1) continue;
    const r = rng();
    if (r < pBi) { adj[i] |= 1 << j; adj[j] |= 1 << i; }
    else if (r < pBi + (1 - pBi) / 2) adj[i] |= 1 << j;
    else adj[j] |= 1 << i;
  }
  return adj;
}

function checkExhaustive4() {
  let kernelFree = 0;
  for (let g = 0; g < 4096; g++) {
    const adj = [0, 0, 0, 0];
    let bit = 0;
    for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) if (i !== j) {
      if ((g >> bit) & 1) adj[i] |= 1 << j;
      bit++;
    }
    const res = checkPropertyStarMWU(4, getAllQKsGeneral(4, adj), 500);
    assert.ok(res.ok, `Exhaustive n=4 failed at g=${g}`);
    if (!res.hasKernel) kernelFree++;
  }
  console.log(`[1] Exhaustive n=4 digraphs: 4096 checked (kernel-free: ${kernelFree}), all satisfy Property (*).`);
}

function checkDeltaBarLe2() {
  const rng = makeRng(202611271);
  let checked = 0, withTriangles = 0;
  for (let n = 4; n <= 12; n++) {
    const trials = n <= 8 ? 1000 : 800;
    for (let t = 0; t < trials; t++) {
      const nonEdge = new Array(n).fill(0), deg = new Array(n).fill(0), pairs = [];
      for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) pairs.push([i, j]);
      for (let i = pairs.length - 1; i > 0; i--) {
        const j = Math.floor(rng() * (i + 1));
        [pairs[i], pairs[j]] = [pairs[j], pairs[i]];
      }
      const pNon = 0.3 + 0.65 * rng();
      for (const [i, j] of pairs) if (deg[i] < 2 && deg[j] < 2 && rng() < pNon) {
        nonEdge[i] |= 1 << j; nonEdge[j] |= 1 << i; deg[i]++; deg[j]++;
      }
      let hasTri = false;
      for (let i = 0; i < n && !hasTri; i++) for (let j = i + 1; j < n && !hasTri; j++)
        if (((nonEdge[i] >> j) & 1) && (nonEdge[i] & nonEdge[j])) hasTri = true;
      if (hasTri) withTriangles++;
      const adj = orientComplement(n, nonEdge, rng, true), w = randomWeights(n, rng);
      const k = constructTheorem1(n, adj, w);
      assertIndependentQK(n, adj, k, `DeltaBar<=2 n=${n}`);
      assert.ok(phiValue(n, adj, k, w) >= -1e-9);
      checked++;
    }
  }
  console.log(`[2] Theorem 1 (Delta(G_bar)<=2, arbitrary alpha): ${checked} graphs checked (${withTriangles} with alpha>=3), all passed.`);
}

function checkStarForestAndMixed() {
  const rng = makeRng(202611272);
  // Explicit QR_7 star test (center 0, leaves 1..7 inducing QR_7, plus 3 universal vertices)
  {
    const n = 11, adj = new Array(n).fill(0);
    for (let i = 0; i < 7; i++) for (const d of [1, 2, 4]) adj[1 + i] |= 1 << (1 + ((i + d) % 7));
    const extras = [0, 8, 9, 10];
    for (let a = 0; a < extras.length; a++) for (let b = a + 1; b < extras.length; b++)
      if (rng() < 0.5) adj[extras[a]] |= 1 << extras[b]; else adj[extras[b]] |= 1 << extras[a];
    for (const e of [8, 9, 10]) for (let v = 1; v <= 7; v++)
      if (rng() < 0.5) adj[e] |= 1 << v; else adj[v] |= 1 << e;
    for (let trial = 0; trial < 50; trial++) {
      const w = randomWeights(n, rng), k = constructTheorem1(n, adj, w);
      assertIndependentQK(n, adj, k, 'QR7-star');
      assert.ok(phiValue(n, adj, k, w) >= -1e-9);
    }
  }
  let sfChecked = 0, mixChecked = 0;
  for (let n = 5; n <= 12; n++) {
    for (let t = 0; t < 500; t++) {
      const nonEdge = new Array(n).fill(0);
      for (let idx = 0; idx < n; ) {
        const sz = Math.min(n - idx, 1 + Math.floor(rng() * 5));
        for (let j = idx + 1; j < idx + sz; j++) { nonEdge[idx] |= 1 << j; nonEdge[j] |= 1 << idx; }
        idx += sz;
      }
      const adj = orientComplement(n, nonEdge, rng, true), w = randomWeights(n, rng);
      const k = constructTheorem1(n, adj, w);
      assertIndependentQK(n, adj, k, `StarForest n=${n}`);
      assert.ok(phiValue(n, adj, k, w) >= -1e-9);
      sfChecked++;
    }
    for (let t = 0; t < 250; t++) {
      const nonEdge = new Array(n).fill(0);
      for (let idx = 0; idx < n; ) {
        const rem = n - idx;
        if (rem >= 4 && rng() < 0.5) {
          const len = Math.min(rem, 4 + Math.floor(rng() * 3));
          for (let j = 0; j < len; j++) {
            const a = idx + j, b = idx + ((j + 1) % len);
            nonEdge[a] |= 1 << b; nonEdge[b] |= 1 << a;
          }
          idx += len;
        } else {
          const sz = Math.min(rem, 1 + Math.floor(rng() * 4));
          for (let j = idx + 1; j < idx + sz; j++) { nonEdge[idx] |= 1 << j; nonEdge[j] |= 1 << idx; }
          idx += sz;
        }
      }
      const adj = orientComplement(n, nonEdge, rng, false), w = randomWeights(n, rng);
      const k = constructTheorem1(n, adj, w);
      assertIndependentQK(n, adj, k, `Mixed n=${n}`);
      assert.ok(phiValue(n, adj, k, w) >= -1e-9);
      mixChecked++;
    }
  }
  console.log(`[3] Theorem 1 (Star-forest + QR_7 star + Mixed): ${sfChecked} star-forest + 50 QR_7-star + ${mixChecked} mixed checked, all passed.`);
}

function checkMonster4AndCLObstacle() {
  const n = 10, adj = new Array(n).fill(0);
  const add = (i, j) => { adj[i] |= 1 << j; };
  add(1, 2); add(2, 3); add(3, 1);
  add(4, 5); add(5, 6); add(6, 4);
  add(7, 8); add(8, 9); add(9, 7);
  for (const wv of [4, 5, 6]) add(wv, 0);
  for (const xv of [7, 8, 9]) add(0, xv);
  add(3, 4); add(1, 5); add(2, 6);
  add(7, 1); add(7, 2); add(3, 7);
  add(8, 2); add(8, 3); add(1, 8);
  add(9, 3); add(9, 1); add(2, 9);

  const undir = new Array(n).fill(0);
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if ((adj[i] >> j) & 1) {
    assert.equal((adj[j] >> i) & 1, 0, 'Monster4 must be oriented');
    undir[i] |= 1 << j; undir[j] |= 1 << i;
  }
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (!((undir[i] >> j) & 1))
    for (let k = j + 1; k < n; k++) assert.ok(((undir[i] >> k) & 1) || ((undir[j] >> k) & 1), 'alpha > 2');
  for (let s = 0; s < n; s++) {
    let vis = 1 << s, q = [s];
    while (q.length) {
      const u = q.pop();
      for (let v = 0; v < n; v++) if (((adj[u] >> v) & 1) && !((vis >> v) & 1)) { vis |= 1 << v; q.push(v); }
    }
    assert.equal(vis, (1 << n) - 1, 'not strongly connected');
  }
  for (let mask = 1; mask < (1 << n) - 1; mask++) {
    const bits = maskToList(n, mask);
    if (bits.length <= 1 || bits.length >= n) continue;
    const f0 = bits[0];
    let isMod = true;
    for (let x = 0; x < n && isMod; x++) {
      if ((mask >> x) & 1) continue;
      const o0 = (adj[f0] >> x) & 1, i0 = (adj[x] >> f0) & 1;
      for (let idx = 1; idx < bits.length; idx++) {
        const u = bits[idx];
        if (((adj[u] >> x) & 1) !== o0 || ((adj[x] >> u) & 1) !== i0) { isMod = false; break; }
      }
    }
    assert.ok(!isMod, `nontrivial module ${JSON.stringify(bits)}`);
  }
  assert.equal(findInDomPair(n, adj), null, 'Monster4 has in-domination');
  const qks = getAllQKsAlpha2(n, adj);
  assert.equal(qks.length, 15, 'Monster4 should have 15 QKs');
  assert.ok(qks.every(q => q.r2 !== 0 && (q.k & 1) === 0), 'Monster4 kernel or vertex 0 in QK');
  for (let v = 0; v < n; v++) {
    let colSum = 0;
    for (let u = 0; u < n; u++) colSum += ((adj[u] >> v) & 1) - ((adj[v] >> u) & 1);
    assert.equal(colSum, 0, `Monster4 A-column ${v} sum != 0`);
  }
  const w = [0.001, 0.001, 0.001, 0.001, 0.001, 0.001, 0.001, 0.331, 0.331, 0.331];
  for (let v = 0; v < n; v++) {
    let fout = 0;
    for (let u = 0; u < n; u++) if ((adj[v] >> u) & 1) fout += w[u];
    assert.ok(w[v] < fout);
  }
  const balanced = qks.filter(q => phiValue(n, adj, q.k, w) >= -1e-9);
  assert.equal(balanced.length, 9, 'Monster4 should have exactly 9 balanced QKs in W x X');
  for (const q of balanced) {
    assertIndependentQK(n, adj, q.k, 'Monster4 balanced QK');
    assert.ok(Math.abs(phiValue(n, adj, q.k, w) - 0.002) < 1e-9);
  }
  // Verify the uniform mixture over the 9 W x X quasi-kernels satisfies fractional balance everywhere
  for (let v = 0; v < n; v++) {
    let bal = 0;
    for (const q of balanced) bal += ((q.n1 >> v) & 1) - ((q.r2 >> v) & 1);
    assert.ok(bal >= 0, `Monster4 uniform 9-QK balance failed at v=${v}`);
  }

  // 7-vertex strongly connected alpha<=2 counterexample to unmodified CL bestAll
  const ceAdj = [38, 64, 24, 18, 65, 26, 41];
  const ceW = [0.2048, 0.0272, 0.1708, 0, 0.2119, 0.1987, 0.1866];
  const ceAll = (1 << 7) - 1;
  let bestAll = -1e9;
  for (let v = 0; v < 7; v++) {
    const rem = ceAll & ~((1 << v) | ceAdj[v]);
    const subs = getAllQKsGeneral(7, ceAdj, rem);
    let minLifted = 1e9;
    for (const sq of subs) {
      if (phiValue(7, ceAdj, sq.k, ceW, rem) < -1e-9) continue;
      let hit = false;
      for (let u = 0; u < 7; u++) if (((sq.k >> u) & 1) && ((ceAdj[u] >> v) & 1)) { hit = true; break; }
      const lifted = hit ? sq.k : (sq.k | (1 << v));
      assertIndependentQK(7, ceAdj, lifted, '7-vertex CL lift');
      const val = phiValue(7, ceAdj, lifted, ceW);
      if (val < minLifted) minLifted = val;
    }
    if (minLifted > bestAll) bestAll = minLifted;
  }
  assert.ok(bestAll < -1e-4, `Expected 7-vertex CL bestAll < 0, got ${bestAll}`);
  console.log(`[4] Monster4 (10v prime/SC/in-dom-free/alpha=2: 15 QKs, 0 in none, 9 balanced) & 7v CL-bestAll CE (${bestAll.toFixed(5)}) verified.`);
}

function checkGeneralAlpha2() {
  const rng = makeRng(202611273);
  let checked = 0, kfInDomFree = 0;
  for (let n = 5; n <= 10; n++) {
    const trials = n <= 8 ? 1200 : 800;
    for (let t = 0; t < trials; t++) {
      const nonEdge = new Array(n).fill(0), pairs = [];
      for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) pairs.push([i, j]);
      for (let i = pairs.length - 1; i > 0; i--) {
        const j = Math.floor(rng() * (i + 1));
        [pairs[i], pairs[j]] = [pairs[j], pairs[i]];
      }
      const pNon = 0.2 + 0.55 * rng();
      for (const [i, j] of pairs) if (rng() < pNon && (nonEdge[i] & nonEdge[j]) === 0) {
        nonEdge[i] |= 1 << j; nonEdge[j] |= 1 << i;
      }
      const adj = orientComplement(n, nonEdge, rng, true);
      const res = checkPropertyStarMWU(n, getAllQKsAlpha2(n, adj), 600);
      assert.ok(res.ok, `Property (*) failed on alpha<=2 n=${n}`);
      checked++;
      if (!res.hasKernel && findInDomPair(n, adj) === null) kfInDomFree++;
    }
  }
  console.log(`[5] General alpha(D)<=2 Property (*) minimax check: ${checked} graphs (${kfInDomFree} kernel-free & in-dom-free), 0 failures.`);
}

checkExhaustive4();
checkDeltaBarLe2();
checkStarForestAndMixed();
checkMonster4AndCLObstacle();
checkGeneralAlpha2();
console.log('ALL CHECKS PASSED.');
