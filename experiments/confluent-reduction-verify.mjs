// Standalone verifier for proofs/合流归约与非邻核推广.md
// Independent QK check: isQuasiKernel(transpose(out), K) from experiments/shared/check.mjs.
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
const popcnt = (x) => { let c = 0; while (x) { x &= x - 1; c++; } return c; };
const maskToArr = (n, m) => { const r = []; for (let i = 0; i < n; i++) if (m & (1 << i)) r.push(i); return r; };

function rebuildIn(n, outM) {
  const inM = new Int32Array(n);
  for (let u = 0; u < n; u++) for (let v = 0; v < n; v++) if (outM[u] & (1 << v)) inM[v] |= 1 << u;
  return inM;
}

function isQKMask(outM, full, kM) {
  let d1 = kM, kk = kM;
  while (kk) { const b = kk & -kk; d1 |= outM[31 - Math.clz32(b)]; kk ^= b; }
  let d2 = d1, dd = d1;
  while (dd) { const b = dd & -dd; d2 |= outM[31 - Math.clz32(b)]; dd ^= b; }
  return d2 === full ? d1 : -1;
}

function verifyQKIndep(n, outM, kM) {
  const adj = Array.from({ length: n }, (_, u) => maskToArr(n, outM[u]));
  assert.equal(isQuasiKernel(transpose(adj), maskToArr(n, kM)), true);
}

function evalMetrics(n, outM, kM, f) {
  let d1 = kM, kk = kM;
  while (kk) { const b = kk & -kk; d1 |= outM[31 - Math.clz32(b)]; kk ^= b; }
  let fTot = 0, w = 0, l1 = 0, l2 = 0;
  for (let i = 0; i < n; i++) {
    fTot += f[i];
    if (d1 & (1 << i)) { w += f[i]; if (!(kM & (1 << i))) l1 += f[i]; } else l2 += f[i];
  }
  return { wRatio: w / fTot, phi: (l1 - l2) / fTot, d1, d1Size: popcnt(d1) };
}

function findOneKernel(n, outM, inM, subMask) {
  const verts = maskToArr(n, subMask);
  let found = -1;
  function dfs(idx, kM, dom, forb) {
    if (found >= 0) return;
    if (dom === subMask) { found = kM; return; }
    if (idx === verts.length) return;
    const v = verts[idx];
    if (!(forb & (1 << v))) dfs(idx + 1, kM | (1 << v), dom | (((1 << v) | outM[v]) & subMask), forb | (1 << v) | outM[v] | inM[v]);
    dfs(idx + 1, kM, dom, forb);
  }
  dfs(0, 0, 0, 0);
  return found;
}

function lemma1QK(n, outM, inM, xMask) {
  const full = (1 << n) - 1;
  let cur = xMask, changed = true;
  const added = [];
  while (changed) {
    changed = false;
    for (let z = 0; z < n; z++) if (!(cur & (1 << z)) && (inM[z] & cur) === 0) {
      cur |= 1 << z; added.push(z); changed = true;
    }
  }
  let kM = 0, dom = 0;
  for (let idx = added.length - 1; idx >= 0; idx--) {
    const z = added[idx];
    if (!(dom & (1 << z))) { kM |= 1 << z; dom |= (1 << z) | outM[z]; }
  }
  const kX = findOneKernel(n, outM, inM, xMask & ~dom);
  assert.ok(kX >= 0);
  const K = kM | kX;
  assert.equal(isQKMask(outM, full, K) & xMask, xMask);
  return K;
}

function reduceR6(n, outM, fIn) {
  let active = (1 << n) - 1, changed = true;
  const f = Float64Array.from(fIn);
  while (changed) {
    changed = false;
    outer: for (let x = 0; x < n; x++) {
      if (!(active & (1 << x))) continue;
      let inX = 1 << x;
      for (let u = 0; u < n; u++) if ((active & (1 << u)) && (outM[u] & (1 << x))) inX |= 1 << u;
      for (let v = 0; v < n; v++) {
        if (v === x || !(active & (1 << v))) continue;
        let inV = 0;
        for (let u = 0; u < n; u++) if ((active & (1 << u)) && (outM[u] & (1 << v))) inV |= 1 << u;
        if ((inX & inV) === inX) { active ^= 1 << v; f[x] += f[v]; f[v] = 0; changed = true; break outer; }
      }
    }
  }
  return { active, f };
}

function induce(n, outM, subMask, f) {
  const verts = maskToArr(n, subMask), m = verts.length;
  const out2 = new Int32Array(m), f2 = new Float64Array(m);
  for (let i = 0; i < m; i++) {
    f2[i] = f[verts[i]];
    for (let j = 0; j < m; j++) if (outM[verts[i]] & (1 << verts[j])) out2[i] |= 1 << j;
  }
  return { verts, m, out2, in2: rebuildIn(m, out2), f2 };
}

const rng = makeRng(20261231);

console.log('=== [1] LEMMA A, LEMMA B & THEOREM U1 (BIDIRECTED NON-NEIGHBORHOOD KERNEL CLASS) ===');
{
  let tested = 0;
  for (let tr = 0; tr < 300; tr++) {
    const n = 7 + (tr % 3); // 7..9
    const outM = new Int32Array(n);
    const orientPair = (u, v, pBidir = 0.25) => {
      const r = rng();
      if (r < pBidir) { outM[u] |= 1 << v; outM[v] |= 1 << u; }
      else if (r < pBidir + (1 - pBidir) / 2) outM[u] |= 1 << v;
      else outM[v] |= 1 << u;
    };
    if (tr % 2 === 0) {
      // Family (a): bidirected Delta(complement) <= 2 (complement is a cycle -> every |I(v)| <= 2!)
      for (let u = 0; u < n; u++) for (let v = u + 1; v < n; v++) {
        const diff = (v - u + n) % n;
        if (diff === 1 || diff === n - 1) continue; // non-adjacent on complement cycle
        orientPair(u, v, 0.25);
      }
    } else {
      // Family (b): semicomplete clique K0 (3v, contains C_3!) + bipartite S (with C_4 & bidir), all K0 <-> S adjacent!
      // Every induced subgraph has I(w) subset S (bipartite -> kernel-perfect!)
      const k0 = 3, sL = 2;
      for (let u = 0; u < k0; u++) for (let v = u + 1; v < k0; v++) orientPair(u, v, 0.15);
      for (let u = 0; u < k0; u++) for (let v = k0; v < n; v++) orientPair(u, v, 0.2);
      for (let u = k0; u < k0 + sL; u++) for (let v = k0 + sL; v < n; v++) {
        if (rng() < 0.45) outM[u] |= 1 << v;
        if (rng() < 0.45) outM[v] |= 1 << u;
      }
    }
    const inM = rebuildIn(n, outM), full = (1 << n) - 1;
    const f = Float64Array.from({ length: n }, () => rng() < 0.2 ? 0 : Math.exp(rng() * 6 - 3));
    if (f.reduce((a, b) => a + b, 0) === 0) f[0] = 1;

    // Verify Lemma B identities (1) & (2)
    let lhs1 = 0, lhs2 = 0, diag = 0, bidir = 0;
    for (let v = 0; v < n; v++) {
      diag += f[v] * f[v];
      let fNoC = f[v], fNoO = 0, fNc = f[v], fM = 0;
      for (let u = 0; u < n; u++) if (u !== v) {
        const vu = !!(outM[v] & (1 << u)), uv = !!(outM[u] & (1 << v));
        if (vu) { fNoC += f[u]; fNoO += f[u]; }
        if (vu || uv) fNc += f[u];
        if (uv && !vu) fM += f[u];
        if (vu && uv && v < u) bidir += f[u] * f[v];
      }
      lhs1 += f[v] * (2 * fNoC - fNc);
      lhs2 += f[v] * (fNoO - fM);
    }
    assert.ok(Math.abs(lhs1 - (diag + 2 * bidir)) < 1e-7);
    assert.ok(Math.abs(lhs2 - 2 * bidir) < 1e-7);

    // Verify Lemma A on original D
    for (let v = 0; v < n; v++) {
      const iv = full ^ ((1 << v) | outM[v] | inM[v]);
      const yv = findOneKernel(n, outM, inM, iv);
      assert.ok(yv >= 0);
      const kv = (1 << v) | yv;
      let d1 = kv, kk = kv;
      while (kk) { const b = kk & -kk; d1 |= outM[31 - Math.clz32(b)]; kk ^= b; }
      let d2 = d1, dd = d1;
      while (dd) { const b = dd & -dd; d2 |= outM[31 - Math.clz32(b)]; dd ^= b; }
      for (let x = 0; x < n; x++) if (!(d2 & (1 << x))) {
        const xm = (1 << x) | inM[x];
        assert.equal(xm & inM[v], xm);
      }
    }

    // Verify Theorem U1 constructively via R6
    const { active, f: fRed } = reduceR6(n, outM, f);
    const { verts, m, out2, in2 } = induce(n, outM, active, fRed);
    const full2 = (1 << m) - 1;
    let foundW = -1, foundStar = -1;
    for (let v = 0; v < m; v++) {
      const yv = findOneKernel(m, out2, in2, full2 ^ ((1 << v) | out2[v] | in2[v]));
      assert.ok(yv >= 0);
      const kv2 = (1 << v) | yv;
      assert.ok(isQKMask(out2, full2, kv2) >= 0);
      let kvOrig = 0;
      for (let i = 0; i < m; i++) if (kv2 & (1 << i)) kvOrig |= 1 << verts[i];
      const ev = evalMetrics(n, outM, kvOrig, f);
      if (ev.wRatio > 0.5 - 1e-11 && foundW < 0) foundW = kvOrig;
      if (ev.phi >= -1e-11 && foundStar < 0) foundStar = kvOrig;
    }
    assert.ok(foundW >= 0 && foundStar >= 0);
    verifyQKIndep(n, outM, foundW);
    verifyQKIndep(n, outM, foundStar);
    tested++;
  }
  console.log(`  Verified Lemma A, Lemma B (1)-(2), and Theorem U1 (W_{1/2} & (*)) on ${tested} bidirected graphs.`);
}

console.log('\n=== [2] THEOREM U3 (ONE-STEP QUASI-KERNEL UPGRADE IDENTITY ON R6-REDUCED C_SKP) ===');
{
  let tested = 0;
  for (let tr = 0; tr < 120; tr++) {
    const tSize = 3 + (tr % 2), sL = 2, sR = 2, n = tSize + sL + sR;
    const outM = new Int32Array(n);
    for (let u = 0; u < tSize; u++) for (let v = u + 1; v < tSize; v++) {
      const r = rng();
      if (r < 0.15) { outM[u] |= 1 << v; outM[v] |= 1 << u; }
      else if (r < 0.575) outM[u] |= 1 << v; else outM[v] |= 1 << u;
    }
    for (let i = 0; i < sL; i++) for (let j = 0; j < sR; j++) {
      if (rng() < 0.45) outM[tSize + i] |= 1 << (tSize + sL + j);
      if (rng() < 0.45) outM[tSize + sL + j] |= 1 << (tSize + i);
    }
    for (let u = 0; u < tSize; u++) for (let v = tSize; v < n; v++) {
      const r = rng();
      if (r < 0.3) outM[u] |= 1 << v; else if (r < 0.6) outM[v] |= 1 << u;
      else if (r < 0.65) { outM[u] |= 1 << v; outM[v] |= 1 << u; }
    }
    const f = Float64Array.from({ length: n }, () => Math.exp(rng() * 6 - 3));
    const { active, f: fRed } = reduceR6(n, outM, f);
    const { m, out2, in2, f2 } = induce(n, outM, active, fRed);
    const full2 = (1 << m) - 1;
    let vKer = 0;
    for (let v = 0; v < m; v++) if (findOneKernel(m, out2, in2, full2 ^ ((1 << v) | out2[v] | in2[v])) >= 0) vKer |= 1 << v;
    const must2 = full2 ^ vKer;
    let maxQK = -1, maxRel = -1;
    const dfs = (idx, kM, forb) => {
      if (idx === m) {
        if (!kM) return;
        let d1 = kM, kk = kM;
        while (kk) { const b = kk & -kk; d1 |= out2[31 - Math.clz32(b)]; kk ^= b; }
        let d2 = d1, dd = d1;
        while (dd) { const b = dd & -dd; d2 |= out2[31 - Math.clz32(b)]; dd ^= b; }
        if ((d2 & must2) === must2) {
          let w = 0; for (let i = 0; i < m; i++) if (d1 & (1 << i)) w += f2[i];
          if (w > maxRel) maxRel = w;
          if (d2 === full2 && w > maxQK) maxQK = w;
        }
        return;
      }
      if (!(forb & (1 << idx))) dfs(idx + 1, kM | (1 << idx), forb | (1 << idx) | out2[idx] | in2[idx]);
      dfs(idx + 1, kM, forb);
    };
    dfs(0, 0, 0);
    assert.ok(Math.abs(maxQK - maxRel) < 1e-9);
    tested++;
  }
  console.log(`  Verified Theorem U3 exact equality on ${tested} R6-reduced C_SKP graphs.`);
}

console.log('\n=== [3] THEOREM U4 / U4* (23v PALEY, 25v-29v C_4 EXTENSIONS & CYCLIC U) ===');
{
  function runU4(n, tSize, outM, f, checkStar) {
    const inM = rebuildIn(n, outM), full = (1 << n) - 1;
    for (let x = tSize; x < n; x++) {
      const xm = (1 << x) | inM[x];
      for (let v = 0; v < tSize; v++) assert.notEqual(xm & inM[v], xm);
    }
    let bestK = -1, bestSize = -1, bestRatio = -1, starK = -1;
    for (let v = 0; v < tSize; v++) {
      const yv = findOneKernel(n, outM, inM, full ^ ((1 << v) | outM[v] | inM[v]));
      assert.ok(yv >= 0);
      const kv = (1 << v) | yv, ev = evalMetrics(n, outM, kv, f);
      if (ev.wRatio > 0.5 + 1e-12 && ev.d1Size > bestSize) { bestSize = ev.d1Size; bestK = kv; bestRatio = ev.wRatio; }
      if (checkStar && ev.phi >= -1e-12 && isQKMask(outM, full, kv) >= 0) starK = kv;
    }
    assert.ok(bestK >= 0);
    verifyQKIndep(n, outM, bestK);
    if (checkStar) { assert.ok(starK >= 0); verifyQKIndep(n, outM, starK); }
    return bestRatio;
  }

  // 23v Paley frontier graph
  {
    const n = 23, outM = new Int32Array(n), add = (u, v) => { outM[u] |= 1 << v; };
    for (let u = 0; u < 7; u++) for (const d of [1, 2, 4]) add(u, (u + d) % 7);
    for (let u = 0; u < 7; u++) { add(u, 7 + 2 * u); add(u, 7 + 2 * u + 1); add(7 + 2 * u, 21); add(7 + 2 * u + 1, 21); }
    add(21, 0); add(21, 22); add(22, 21);
    const f = Float64Array.from({ length: n }, (_, i) => i < 7 ? 1 : 0);
    assert.ok(Math.abs(runU4(n, 7, outM, f, true) - 4 / 7) < 1e-9);
    console.log('  23v Paley frontier graph: Theorem U4 & U4* verified (4/7).');
  }
  // 25v-29v bipartite U = I_0 U B (|B|=2..4 with C_4 & bidir)
  let ext = 0;
  for (const bSize of [2, 3, 4]) for (let tr = 0; tr < 15; tr++) {
    const n = 21 + bSize, outM = new Int32Array(n), add = (u, v) => { outM[u] |= 1 << v; };
    for (let u = 0; u < 7; u++) for (const d of [1, 2, 4]) add(u, (u + d) % 7);
    for (let u = 0; u < 7; u++) { add(u, 7 + 2 * u); add(u, 7 + 2 * u + 1); }
    for (let b = 0; b < bSize; b++) {
      const bv = 21 + b;
      add(7 + (2 * b) % 14, bv); add(7 + (2 * b + 1) % 14, bv); add(bv, 7 + (2 * b + 2) % 14);
      if (b % 2 === 0) add(bv, 7 + (2 * b) % 14);
      for (let k = 0; k < 3; k++) if (rng() < 0.6) add(bv, (rng() * 7) | 0);
      for (let k = 0; k < 2; k++) if (rng() < 0.4) add((rng() * 7) | 0, bv);
    }
    const f = Float64Array.from({ length: n }, (_, i) => i < 7 ? 1 + rng() * 3 : 0);
    assert.ok(runU4(n, 7, outM, f, false) > 0.5);
    ext++;
  }
  console.log(`  25v-29v QR_7 + bipartite C_4/bidir U: Theorem U4 verified on ${ext} graphs.`);
  // 13v QR_7 + cyclic U with TWO C_3's
  {
    const n = 13, outM = new Int32Array(n), add = (u, v) => { outM[u] |= 1 << v; };
    for (let u = 0; u < 7; u++) for (const d of [1, 2, 4]) add(u, (u + d) % 7);
    add(7, 8); add(8, 9); add(9, 7); add(10, 11); add(11, 12); add(12, 10);
    for (let v = 0; v < 7; v++) { add(v, 7 + (v % 3)); add(10 + (v % 3), v); }
    const f = Float64Array.from({ length: n }, (_, i) => i < 7 ? 1 : 0);
    assert.ok(runU4(n, 7, outM, f, true) > 0.5);
    console.log('  13v QR_7 + cyclic U (two C_3s): Theorem U4 & U4* verified.');
  }
}

console.log('\n=== [4] THEOREM U2* (kp-del(D) <= 3, ARBITRARY f >= 0, C_4/C_6 & BIDIR) ===');
{
  let tested = 0;
  for (let tr = 0; tr < 300; tr++) {
    const n = 9, outM = new Int32Array(n);
    outM[0] = 2; outM[1] = 4; outM[2] = 1;
    for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
      if (rng() < 0.45) outM[3 + i] |= 1 << (6 + j);
      if (rng() < 0.45) outM[6 + j] |= 1 << (3 + i);
    }
    for (let u = 0; u < 3; u++) for (let v = 3; v < 9; v++) {
      const r = rng();
      if (r < 0.55) outM[v] |= 1 << u; else if (r < 0.8) outM[u] |= 1 << v;
      else if (r < 0.85) { outM[u] |= 1 << v; outM[v] |= 1 << u; }
    }
    const f = Float64Array.from({ length: n }, (_, i) => i < 3 ? (0.15 + rng() * 0.1) : (rng() < 0.2 ? 0 : rng() * 0.2));
    const { active, f: fRed } = reduceR6(n, outM, f);
    const { verts, m, out2, in2 } = induce(n, outM, active, fRed);
    const full2 = (1 << m) - 1;
    const tVerts = []; for (let i = 0; i < m; i++) if (verts[i] < 3) tVerts.push(i);
    let tMask = 0; for (const i of tVerts) tMask |= 1 << i;
    const sMask = full2 ^ tMask;
    const cands = [];
    if (sMask) cands.push(lemma1QK(m, out2, in2, sMask));
    if (tVerts.length < 3 || findOneKernel(m, out2, in2, tMask) >= 0) {
      if (tMask) cands.push(lemma1QK(m, out2, in2, tMask));
    } else {
      for (const v of tVerts) cands.push((1 << v) | findOneKernel(m, out2, in2, full2 ^ ((1 << v) | out2[v] | in2[v])));
      for (const drop of tVerts) {
        const aMask = tMask ^ (1 << drop);
        let sA = 0;
        for (let s = 0; s < m; s++) if (sMask & (1 << s)) {
          let ok = true;
          for (const v of tVerts) if (v !== drop && (!(out2[s] & (1 << v)) || (out2[v] & (1 << s)))) { ok = false; break; }
          if (ok) sA |= 1 << s;
        }
        cands.push(lemma1QK(m, out2, in2, sA | aMask));
      }
    }
    let winOrig = -1;
    for (const k2 of cands) {
      let kOrig = 0;
      for (let i = 0; i < m; i++) if (k2 & (1 << i)) kOrig |= 1 << verts[i];
      if (evalMetrics(n, outM, kOrig, f).wRatio >= 0.5 - 1e-11) { winOrig = kOrig; break; }
    }
    assert.ok(winOrig >= 0);
    verifyQKIndep(n, outM, winOrig);
    tested++;
  }
  console.log(`  Verified Theorem U2* constructive proof on ${tested} graphs (T=C_3 + 6v C_4/C_6/bidir S).`);
}

console.log('\n=== [5] BOUNDARY EXAMPLES, Z1/Z3 VERIFICATION & EXACT LP CERTIFICATES ===');
{
  // (a) 5v Rosetta Stone
  {
    const n = 5, outM = new Int32Array([10, 12, 9, 16, 7]), f = [0.18, 0.18, 0.18, 0.01, 0.45];
    assert.equal(reduceR6(n, outM, f).active, 31);
    for (let v = 0; v < 3; v++) { verifyQKIndep(n, outM, 1 << v); assert.ok(evalMetrics(n, outM, 1 << v, f).wRatio < 0.38); }
    verifyQKIndep(n, outM, 8); assert.ok(evalMetrics(n, outM, 8, f).wRatio < 0.47);
    verifyQKIndep(n, outM, 16); assert.ok(evalMetrics(n, outM, 16, f).wRatio > 0.98);
  }
  // (b) 9v C_4 U {b1,b2}
  {
    const n = 9, outM = new Int32Array([2, 4, 1, 144, 288, 192, 264, 7, 7]), f = [10, 10, 10, 0, 0, 0, 0, 10, 10];
    assert.equal(reduceR6(n, outM, f).active, 511);
    assert.equal(isQKMask(outM, 511, 384), -1);
    verifyQKIndep(n, outM, (1 << 3) | (1 << 5) | (1 << 8));
  }
  // (c) 7v s*-blocked R6-reduced C_SKP
  {
    const n = 7, outM = new Int32Array([18, 36, 9, 64, 64, 64, 0]);
    assert.equal(reduceR6(n, outM, [1, 1, 1, 1, 1, 1, 1]).active, 127);
    let hits = 0;
    for (let kM = 64; kM < 128; kM++) {
      let ok = true;
      for (let u = 0; u < 7 && ok; u++) if ((kM & (1 << u)) && (outM[u] & kM)) ok = false;
      if (ok && isQKMask(outM, 127, kM) >= 0) hits++;
    }
    assert.equal(hits, 0);
  }
  // (d) 9v Z1+R6-reduced T=C_3 + cyclic U where 0 in 0 QKs
  {
    const n = 9, outM = new Int32Array([2, 4, 1, 148, 292, 76, 1 | 32, 1 | 8, 1 | 16]);
    for (let u = 3; u < 9; u++) assert.ok((outM[u] & 7) !== 0);
    assert.equal(reduceR6(n, outM, [1, 1, 1, 0, 0, 0, 0, 0, 0]).active, 511);
    let hits0 = 0;
    for (let kM = 1; kM < 512; kM += 2) {
      let ok = true;
      for (let u = 0; u < 9 && ok; u++) if ((kM & (1 << u)) && (outM[u] & kM)) ok = false;
      if (ok && isQKMask(outM, 511, kM) >= 0) hits0++;
    }
    assert.equal(hits0, 0);
    verifyQKIndep(n, outM, (1 << 1) | (1 << 3) | (1 << 6));
  }
  // (e) Exact 11/23 dual certificate on m=4 strong tournament
  {
    const outM = [8, 1, 3, 6], wT = [4, 3, 2, 3];
    const types = [[5, 1], [7, 2], [11, 2], [12, 1], [13, 2], [14, 3]];
    let maxRow = 11; // S has weight 11
    for (let v = 0; v < 4; v++) {
      let s = 0;
      for (let u = 0; u < 4; u++) if (u === v || (outM[v] & (1 << u))) s += wT[u];
      for (const [M, w] of types) if (!(M & (1 << v))) s += w;
      if (s > maxRow) maxRow = s;
    }
    for (let A = 1; A < 16; A++) {
      let seen = 0, trans = true;
      for (let i = 0; i < 4; i++) if (A & (1 << i)) {
        const d = popcnt(outM[i] & A);
        if (seen & (1 << d)) { trans = false; break; }
        seen |= 1 << d;
      }
      if (!trans) continue;
      let s = 0;
      for (let u = 0; u < 4; u++) if (A & (1 << u)) s += wT[u];
      for (const [M, w] of types) if ((M & A) === A) s += w;
      if (s > maxRow) maxRow = s;
    }
    assert.equal(maxRow, 11);
  }
  // (f) 28v QR_7 + C(7,5) exact bound & Z1/Z3 lifting check on cyclic U
  {
    const comb = (n, k) => { let r = 1; for (let i = 1; i <= k; i++) r = r * (n - i + 1) / i; return r; };
    assert.ok((4 / 7) * 0.51 + (2 / 7) * 0.49 < 0.5);
    for (let a = 1; a <= 5; a++) assert.ok((a / 7) * 0.51 + (comb(7 - a, 5 - a) / 21) * 0.49 < 0.5);
    // Z1 & Z3 constructive lift check: T=C_3 + U_sink (C_3, T->U_sink) + U_src (C_3, U_src->T)
    const n = 9, outM = new Int32Array([2 | 8, 4 | 16, 1 | 32, 16, 32, 8, 128 | 1, 256 | 2, 64 | 4]);
    // Z3 picks QK {6} of U_src={6,7,8} (covers 0 in T!), deletes {6,7,8,0}; Z1 picks {3} of U_sink={3,4,5}, lifts to QK {6,1,3}!
    verifyQKIndep(n, outM, (1 << 6) | (1 << 1) | (1 << 3));
  }
  console.log('  Verified 5v Rosetta Stone, 9v C_4, 7v s*-blocked, 9v Z1+R6 cyclic-U, 11/23 dual, 28v QR_7+C(7,5), and Z1/Z3 lift.');
}
console.log('\nALL CONFLUENT REDUCTION VERIFICATIONS PASSED.');
