// Standalone verifier for proofs/半完全核心与二分外图的加权半支配定理.md
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
const maskToArr = (n, m) => { const r = []; for (let i = 0; i < n; i++) if (m & (1 << i)) r.push(i); return r; };

function rebuildIn(n, outM) {
  const inM = new Int32Array(n);
  for (let u = 0; u < n; u++) for (let v = 0; v < n; v++) if (outM[u] & (1 << v)) inM[v] |= 1 << u;
  return inM;
}
function evalMask(n, outM, f, kM) {
  let d1 = kM, kk = kM;
  while (kk) { const b = kk & -kk; d1 |= outM[31 - Math.clz32(b)]; kk ^= b; }
  let d2 = d1, dd = d1;
  while (dd) { const b = dd & -dd; d2 |= outM[31 - Math.clz32(b)]; dd ^= b; }
  let w = 0; for (let i = 0; i < n; i++) if (d1 & (1 << i)) w += f[i];
  return { w, d1, d2 };
}
function verifyQKIndep(n, outM, kM) {
  const adj = Array.from({ length: n }, (_, u) => maskToArr(n, outM[u]));
  assert.equal(isQuasiKernel(transpose(adj), maskToArr(n, kM)), true);
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
function isKernelPerfect(n, outM, inM, subMask) {
  for (let sub = subMask; sub > 0; sub = (sub - 1) & subMask) {
    if (findOneKernel(n, outM, inM, sub) < 0) return false;
  }
  return true;
}
function hasOddDirectedCycle(n, outM, subMask) {
  const verts = maskToArr(n, subMask), reach = new Int32Array(n);
  for (const s of verts) {
    let r = 1 << s, q = 1 << s;
    while (q) { const b = q & -q; const u = 31 - Math.clz32(b); q ^= b; const nxt = (outM[u] & subMask) & ~r; r |= nxt; q |= nxt; }
    reach[s] = r;
  }
  const color = new Int8Array(n).fill(-1);
  for (const s of verts) {
    if (color[s] !== -1) continue;
    let scc = 0;
    for (const u of verts) if ((reach[s] & (1 << u)) && (reach[u] & (1 << s))) scc |= 1 << u;
    const q = [s]; color[s] = 0;
    for (let qi = 0; qi < q.length; qi++) {
      const u = q[qi];
      for (const v of maskToArr(n, outM[u] & scc)) {
        if (color[v] === -1) { color[v] = 1 - color[u]; q.push(v); }
        else if (color[v] === color[u]) return true;
      }
    }
  }
  return false;
}
function lemma1QK(n, outM, inM, xMask) {
  let cur = xMask, changed = true;
  const added = [];
  while (changed) {
    changed = false;
    for (let z = 0; z < n; z++) if (!(cur & (1 << z)) && (inM[z] & cur) === 0) { cur |= 1 << z; added.push(z); changed = true; }
  }
  let kM = 0, dom = 0;
  for (let idx = added.length - 1; idx >= 0; idx--) {
    const z = added[idx];
    if (!(dom & (1 << z))) { kM |= 1 << z; dom |= (1 << z) | outM[z]; }
  }
  const kX = findOneKernel(n, outM, inM, xMask & ~dom);
  assert.ok(kX >= 0);
  return kM | kX;
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
function findSourceSCC(m, outM, subMask) {
  const verts = maskToArr(m, subMask), reach = new Int32Array(m);
  for (const s of verts) {
    let r = 1 << s, q = 1 << s;
    while (q) { const b = q & -q; const u = 31 - Math.clz32(b); q ^= b; const nxt = (outM[u] & subMask) & ~r; r |= nxt; q |= nxt; }
    reach[s] = r;
  }
  for (const s of verts) {
    let scc = 0;
    for (const u of verts) if ((reach[s] & (1 << u)) && (reach[u] & (1 << s))) scc |= 1 << u;
    let hasIn = false;
    for (const u of verts) if (!(scc & (1 << u)) && (outM[u] & scc)) { hasIn = true; break; }
    if (!hasIn) return scc;
  }
  throw new Error('No source SCC');
}

// Replay Theorem O1-U* (unified proof for O1-A, O1-R, and mixed DAGs of both!)
function replayO1U(n, tSize, outM, fIn) {
  const { active, f: fRed } = reduceR6(n, outM, fIn);
  const verts = maskToArr(n, active), m = verts.length;
  const out2 = new Int32Array(m), f2 = new Float64Array(m);
  let fTot = 0;
  for (let i = 0; i < m; i++) {
    f2[i] = fRed[verts[i]]; fTot += f2[i];
    for (let j = 0; j < m; j++) if (outM[verts[i]] & (1 << verts[j])) out2[i] |= 1 << j;
  }
  for (let i = 0; i < m; i++) f2[i] /= fTot;
  const in2 = rebuildIn(m, out2), full2 = (1 << m) - 1;
  let tMask = 0; for (let i = 0; i < m; i++) if (verts[i] < tSize) tMask |= 1 << i;
  const sMask = full2 ^ tMask;
  let k2Win = -1, branch = '';
  let fS = 0; for (let i = 0; i < m; i++) if (sMask & (1 << i)) fS += f2[i];
  if (fS >= 0.5 - 1e-11) { k2Win = lemma1QK(m, out2, in2, sMask); branch = 'S'; }
  const mTilde = new Float64Array(m);
  if (k2Win < 0) {
    for (let v = 0; v < m; v++) if (tMask & (1 << v)) {
      const yv = findOneKernel(m, out2, in2, full2 ^ ((1 << v) | out2[v] | in2[v]));
      assert.ok(yv >= 0);
      const kv = (1 << v) | yv, ev = evalMask(m, out2, f2, kv);
      if (ev.w >= 0.5 - 1e-11) { k2Win = kv; branch = 'Kv'; break; }
      for (let i = 0; i < m; i++) if ((sMask & (1 << i)) && !(ev.d1 & (1 << i))) mTilde[i] += f2[v];
    }
  }
  if (k2Win < 0) {
    // Theorem 2 (SCC-Peeling Superlevel Theorem)
    const mus = [...new Set(maskToArr(m, sMask).filter(s => f2[s] > 1e-15 && mTilde[s] > 1e-12).map(s => mTilde[s]))].sort((a, b) => b - a);
    let winA = -1, winKind = '';
    outer: for (const mu of mus) {
      let hM = 0, fH = 0;
      for (let i = 0; i < m; i++) if ((sMask & (1 << i)) && mTilde[i] >= mu - 1e-12) { hM |= 1 << i; fH += f2[i]; }
      const c0 = findSourceSCC(m, out2, hM), c0Arr = maskToArr(m, c0);
      // Condition (a): check if some a* in C_0 has M_{C_0}(a*) = empty
      const aStar = c0Arr.find(u => (((in2[u] & ~out2[u]) & c0) === 0));
      if (aStar !== undefined) {
        if (fH + mTilde[aStar] > 0.5 - 1e-11) { winA = aStar; winKind = c0Arr.length === 1 ? 'Ka_size1' : 'Ka_strictFree'; break outer; }
      } else {
        // Condition (b): scan a in C_0
        for (const a of c0Arr) {
          const mC0a = (in2[a] & ~out2[a]) & c0;
          let fM = 0; for (let i = 0; i < m; i++) if (mC0a & (1 << i)) fM += f2[i];
          if (fH - fM + mTilde[a] > 0.5 - 1e-11) { winA = a; winKind = 'Ka_bipSCC'; break outer; }
        }
      }
    }
    assert.ok(winA >= 0, 'Theorem 2 must find winning (mu, C_0, a)');
    const b0 = findOneKernel(m, out2, in2, sMask & ~((1 << winA) | out2[winA] | in2[winA]));
    assert.ok(b0 >= 0);
    let kCand = (1 << winA) | b0;
    const ev = evalMask(m, out2, f2, kCand);
    assert.ok(ev.w >= 0.5 - 1e-10);
    assert.equal(ev.d2 & sMask, sMask, 'Single-vertex K_a must 2-cover all of S');
    branch = winKind;
    const remT = tMask & ~ev.d2;
    if (remT) {
      const x = 31 - Math.clz32(remT & -remT);
      kCand = (1 << x) | findOneKernel(m, out2, in2, full2 ^ ((1 << x) | out2[x] | in2[x]));
      branch += '+U3';
    }
    assert.equal(evalMask(m, out2, f2, kCand).d2, full2);
    k2Win = kCand;
  }
  let kOrig = 0;
  for (let i = 0; i < m; i++) if (k2Win & (1 << i)) kOrig |= 1 << verts[i];
  verifyQKIndep(n, outM, kOrig);
  const evOrig = evalMask(n, outM, fIn, kOrig);
  const totOrig = fIn.reduce((a, b) => a + b, 0);
  assert.ok(evOrig.w / totOrig >= 0.5 - 1e-10);
  return { branch, ratio: evOrig.w / totOrig };
}

const rng = makeRng(20261237);

console.log('=== [1] COROLLARY 1: 5-LINE BIDIRECTED SPLIT DIGRAPH THEOREM (200 GRAPHS) ===');
{
  for (let tr = 0; tr < 200; tr++) {
    const tSize = 4 + (tr % 4), n = tSize + 5, outM = new Int32Array(n);
    for (let u = 0; u < tSize; u++) for (let v = u + 1; v < tSize; v++) {
      const r = rng();
      if (r < 0.2) { outM[u] |= 1 << v; outM[v] |= 1 << u; }
      else if (r < 0.6) outM[u] |= 1 << v; else outM[v] |= 1 << u;
    }
    for (let u = 0; u < tSize; u++) for (let v = tSize; v < n; v++) {
      const r = rng();
      if (r < 0.35) outM[v] |= 1 << u; else if (r < 0.7) outM[u] |= 1 << v;
      else if (r < 0.78) { outM[u] |= 1 << v; outM[v] |= 1 << u; }
    }
    const f = Float64Array.from({ length: n }, () => rng() < 0.2 ? 0 : Math.exp(rng() * 6 - 3));
    if (f.reduce((a, b) => a + b, 0) === 0) f[0] = 1;
    const { active, f: fRed } = reduceR6(n, outM, f);
    const verts = maskToArr(n, active), m = verts.length;
    const out2 = new Int32Array(m), f2 = new Float64Array(m);
    let fTot = 0;
    for (let i = 0; i < m; i++) {
      f2[i] = fRed[verts[i]]; fTot += f2[i];
      for (let j = 0; j < m; j++) if (outM[verts[i]] & (1 << verts[j])) out2[i] |= 1 << j;
    }
    const in2 = rebuildIn(m, out2), full2 = (1 << m) - 1;
    let tMask = 0; for (let i = 0; i < m; i++) if (verts[i] < tSize) tMask |= 1 << i;
    const sMask = full2 ^ tMask;
    let win2 = -1;
    if (sMask) {
      const ev = evalMask(m, out2, f2, sMask);
      if (ev.w >= 0.5 * fTot - 1e-10) {
        const remT = tMask & ~ev.d2;
        if (remT) { const x = 31 - Math.clz32(remT & -remT); win2 = (1 << x) | (full2 ^ ((1 << x) | out2[x] | in2[x])); }
        else win2 = sMask;
      }
    }
    if (win2 < 0) {
      for (let v = 0; v < m; v++) if (tMask & (1 << v)) {
        const kv = (1 << v) | (full2 ^ ((1 << v) | out2[v] | in2[v]));
        if (evalMask(m, out2, f2, kv).w >= 0.5 * fTot - 1e-10) { win2 = kv; break; }
      }
    }
    assert.ok(win2 >= 0);
    let kOrig = 0; for (let i = 0; i < m; i++) if (win2 & (1 << i)) kOrig |= 1 << verts[i];
    verifyQKIndep(n, outM, kOrig);
  }
  console.log('  Verified 5-line bidirected split digraph proof on 200 graphs.');
}

console.log('\n=== [2] THEOREM O1-R: SEMICOMPLETE + NON-BIPARTITE ODD-DIRECTED-CYCLE-FREE S (500 GRAPHS) ===');
{
  const counts = {};
  let nonBipCount = 0;
  for (let tr = 0; tr < 500; tr++) {
    const useC6 = tr % 3 === 1, n = 15, tSize = 7;
    const outM = new Int32Array(n), add = (u, v) => { outM[u] |= 1 << v; };
    for (let u = 0; u < 7; u++) for (const d of [1, 2, 4]) add(u, (u + d) % 7);
    if (!useC6) { add(7, 8); add(8, 9); add(9, 10); add(10, 7); }
    else { add(7, 8); add(8, 9); add(9, 10); add(10, 11); add(11, 12); add(12, 7); }
    if (tr % 4 === 0) { add(8, 7); add(10, 9); } // bidirected C_2 inside bipartite SCC
    const heavy = useC6 ? [7, 8, 9, 10, 11, 12] : [7, 8, 9, 10];
    // Non-bipartite odd-directed-cycle-free blockers above heavy SCC (13<->14 + triangles 13->14->7, 13->7, 13->9)
    add(13, 14); add(14, 13); add(14, 7); add(13, 7); add(13, 9); add(14, 8); add(13, 10);
    if (!useC6) { add(11, 12); add(12, 11); add(11, 8); add(12, 10); }
    else { add(13, 11); add(14, 12); }
    assert.equal(hasOddDirectedCycle(n, outM, ((1 << n) - 1) ^ 127), false);
    nonBipCount++; // {13, 14, 7} forms an undirected triangle (non-bipartite!), still 0 odd directed cycles
    for (const s of heavy) for (let v = 0; v < 7; v++) add(s, v);
    for (let s = 7; s < n; s++) if (!heavy.includes(s)) for (let v = 0; v < 7; v++) add(v, s);
    // Occasional missing cross-arcs to also exercise +U3 and mixed branches
    if (tr % 5 === 0) { outM[7] ^= 1 << 0; add(0, 7); }
    const f = new Float64Array(n), sTot = 0.40 + rng() * 0.08;
    for (let v = 0; v < 7; v++) f[v] = (1 - sTot) / 7;
    for (let s = 7; s < n; s++) f[s] = heavy.includes(s) ? (sTot - 0.01) / heavy.length : 0.01 / (8 - heavy.length);
    const { branch } = replayO1U(n, tSize, outM, f);
    counts[branch] = (counts[branch] || 0) + 1;
  }
  assert.ok((counts['Ka_bipSCC'] || 0) >= 300, `Expected >=300 Ka_bipSCC hits, got ${JSON.stringify(counts)}`);
  console.log(`  Verified Theorem O1-R on 500 graphs (non-bipartite: ${nonBipCount}). Branches:`, JSON.stringify(counts));
}

console.log('\n=== [3] THEOREM O1-A & MIXED DAG (BIDIR CLIQUES + C_4, 300 GRAPHS) ===');
{
  const counts = {};
  for (let tr = 0; tr < 300; tr++) {
    const n = 17, tSize = 7, outM = new Int32Array(n), add = (u, v) => { outM[u] |= 1 << v; };
    for (let u = 0; u < 7; u++) for (const d of [1, 2, 4]) add(u, (u + d) % 7);
    // Block 1: {7,8,9,10} strict-cycle-free with bidirected clique; Block 2: {11,12,13,14} C_4; R6 guards: 15, 16
    for (let i = 7; i <= 10; i++) for (let j = i + 1; j <= 10; j++) {
      if (rng() < 0.75) { add(i, j); add(j, i); } else add(i, j);
    }
    add(11, 12); add(12, 13); add(13, 14); add(14, 11);
    for (let u = 7; u <= 10; u++) for (let v = 11; v <= 14; v++) if (rng() < 0.4) add(u, v);
    for (let u = 7; u <= 10; u++) add(15, u);
    for (let v = 11; v <= 14; v++) add(16, v);
    for (let v = 0; v < 7; v++) { add(v, 15); add(v, 16); }
    const heavyClique = tr % 2 === 0;
    for (let s = 7; s <= 10; s++) for (let v = 0; v < 7; v++) if (heavyClique) add(s, v); else add(v, s);
    for (let s = 11; s <= 14; s++) for (let v = 0; v < 7; v++) if (heavyClique) add(v, s); else add(s, v);
    const f = new Float64Array(n), sTot = 0.40 + rng() * 0.06;
    for (let v = 0; v < 7; v++) f[v] = (1 - sTot) / 7;
    for (let s = 7; s <= 10; s++) f[s] = heavyClique ? (sTot - 0.01) / 4 : 0.002;
    for (let s = 11; s <= 14; s++) f[s] = heavyClique ? 0.002 : (sTot - 0.01) / 4;
    f[15] = 0.001; f[16] = 0.001;
    const { branch } = replayO1U(n, tSize, outM, f);
    counts[branch] = (counts[branch] || 0) + 1;
  }
  assert.ok((counts['Ka_strictFree'] || 0) >= 120 && (counts['Ka_bipSCC'] || 0) >= 120, `Got ${JSON.stringify(counts)}`);
  console.log('  Verified Theorem O1-A & mixed O1-U* on 300 graphs. Branches:', JSON.stringify(counts));
}

console.log('\n=== [4] COROLLARY 2: MATCHING-SUPPORT C_4 CONFLUENT GRAPHS (23-29v WITH CROSS-R6) ===');
{
  let tested = 0;
  for (const bSize of [2, 3, 4]) for (let tr = 0; tr < 10; tr++) {
    const n = 21 + bSize, outM = new Int32Array(n), add = (u, v) => { outM[u] |= 1 << v; };
    for (let u = 0; u < 7; u++) for (const d of [1, 2, 4]) add(u, (u + d) % 7);
    for (let u = 0; u < 7; u++) { add(u, 7 + 2 * u); add(u, 7 + 2 * u + 1); }
    add(3, 21); add(5, 21); add(6, 21); add(21, 0);
    add(21, 7); add(7, 22); add(22, 8); add(8, 21); add(8, 0);
    for (let b = 1; b < bSize; b++) {
      const bv = 21 + b;
      add(7 + (2 * b) % 14, bv); add(bv, 7 + (2 * b + 1) % 14);
      if (b % 2 === 1) add(7 + (2 * b + 1) % 14, bv);
      add(bv, b % 7);
    }
    const f = Float64Array.from({ length: n }, (_, i) => i < 7 ? 1 : 0);
    const inM = rebuildIn(n, outM), x21 = (1 << 21) | inM[21];
    assert.equal(x21 & inM[0], x21); // confirm cross-R6 (21 => 0)
    const { ratio } = replayO1U(n, 7, outM, f);
    assert.ok(ratio >= 4 / 7 - 1e-9);
    tested++;
  }
  console.log(`  Verified Corollary 2 (C_4 + cross-R6) on ${tested} graphs (23-29v).`);
}

console.log('\n=== [5] EXPLICIT BOUNDARY EXAMPLES (23v NON-BIPARTITE C_6, 17v DEEP-CHAIN, 5v H_5) ===');
{
  // (a) 23v non-bipartite odd-directed-cycle-free C_6 obstruction: breaks multi-vertex A_0 U B_0, solved by O1-R!
  {
    const n = 23, full = (1 << n) - 1, tMask = (1 << 9) - 1, sMask = full ^ tMask;
    const outM = new Int32Array(n), add = (u, v) => { outM[u] |= 1 << v; };
    for (let u = 0; u < 9; u++) for (const d of [1, 2, 3, 4]) add(u, (u + d) % 9);
    for (let i = 0; i < 6; i++) add(9 + i, 9 + ((i + 1) % 6));
    add(15, 9); add(15, 11); add(15, 13);
    add(16, 15); add(16, 9); add(17, 15); add(17, 11); add(18, 15); add(18, 13);
    add(19, 10); add(19, 12); add(19, 14);
    add(20, 19); add(20, 10); add(21, 19); add(21, 12); add(22, 19); add(22, 14);
    for (let s = 9; s <= 14; s++) for (let v = 0; v < 9; v++) add(s, v);
    for (const [y, ivs] of [[16,[0,1,2]],[17,[3,4,5]],[18,[6,7,8]],[20,[0,1,2]],[21,[3,4,5]],[22,[6,7,8]]])
      for (let v = 0; v < 9; v++) if (!ivs.includes(v)) add(v, y);
    const inM = rebuildIn(n, outM);
    assert.equal(isKernelPerfect(n, outM, inM, sMask), true);
    assert.equal(hasOddDirectedCycle(n, outM, sMask), false);
    const f = new Float64Array(n);
    for (let v = 0; v < 9; v++) f[v] = 0.56 / 9;
    for (let s = 9; s <= 14; s++) f[s] = 0.072;
    for (let s = 15; s < n; s++) f[s] = 0.001;
    assert.equal(reduceR6(n, outM, f).active, full);
    // Confirm ALL K_v < 0.5 and BOTH 1-kernels of C_6 miss S in A_0 U B_0!
    for (let v = 0; v < 9; v++) {
      const kv = (1 << v) | findOneKernel(n, outM, inM, full ^ ((1 << v) | outM[v] | inM[v]));
      assert.ok(evalMask(n, outM, f, kv).w < 0.47);
    }
    for (const [a0, miss] of [[(1<<9)|(1<<11)|(1<<13), 15], [(1<<10)|(1<<12)|(1<<14), 19]]) {
      let adj = a0, aa = a0; while (aa) { const b = aa & -aa; const u = 31 - Math.clz32(b); adj |= outM[u] | inM[u]; aa ^= b; }
      const K = a0 | findOneKernel(n, outM, inM, sMask & ~adj);
      assert.equal(sMask & ~evalMask(n, outM, f, K).d2, 1 << miss);
    }
    const { branch, ratio } = replayO1U(n, 9, outM, f);
    assert.equal(branch, 'Ka_bipSCC'); assert.ok(ratio > 0.998);
    console.log(`  23v non-bipartite C_6 obstruction verified: O1-R branch=${branch}, ratio=${ratio.toFixed(4)}.`);
  }
  // (b) 17v deep-chain R6-reduced acyclic-S example
  {
    const n = 17, outM = new Int32Array(n), add = (u, v) => { outM[u] |= 1 << v; };
    for (let u = 0; u < 7; u++) for (const d of [1, 2, 4]) add(u, (u + d) % 7);
    add(7, 8); add(8, 16);
    for (let v = 0; v < 7; v++) add(8, 9 + v);
    for (let i = 0; i < 7; i++) for (let j = i + 1; j < 7; j++) add(9 + i, 9 + j);
    for (let v = 0; v < 7; v++) add(9 + v, 16);
    for (let v = 0; v < 7; v++) {
      add(16, v); add(9 + v, v);
      for (let u = 0; u < 7; u++) if (u !== v) add(u, 9 + v);
      add(v, 7); if (v === 0) add(8, 0); else add(v, 8);
    }
    const f = new Float64Array(n);
    for (let v = 0; v < 7; v++) f[v] = 0.59 / 7;
    f[7] = 0.0001; f[8] = 0.0002;
    for (let v = 0; v < 7; v++) f[9 + v] = 0.0005 + 0.0001 * v;
    f[16] = 1 - f.reduce((a, b) => a + b, 0);
    assert.equal(reduceR6(n, outM, f).active, (1 << n) - 1);
    const { branch, ratio } = replayO1U(n, 7, outM, f);
    assert.ok(ratio > 0.99);
    console.log(`  17v deep-chain verified: O1-A branch=${branch}, ratio=${ratio.toFixed(4)}.`);
  }
  // (c) 5v chorded odd-cycle strongly connected kernel-perfect H_5 (pinpoints O1'')
  {
    const n = 5, full = 31, outM = new Int32Array([10, 21, 24, 17, 1]); // 0->1,3; 1->0,2,4; 2->3,4; 3->0,4; 4->0
    const inM = rebuildIn(n, outM);
    assert.equal(isKernelPerfect(n, outM, inM, full), true);
    assert.equal(hasOddDirectedCycle(n, outM, full), true);
    assert.equal(full ^ ((1 << 4) | outM[4] | inM[4]), 0); // I(4) = empty
    assert.equal(full & ~evalMask(n, outM, new Float64Array(5), 1 << 4).d2, 1 << 2); // misses 2!
    console.log('  5v chorded odd-cycle kernel-perfect H_5 verified: KP=true, K_4 misses vertex 2 (pinpoints O1\'\').');
  }
}

console.log('\nALL SEMICOMPLETE + ODD-CYCLE-FREE / STRICT-CYCLE-FREE VERIFICATIONS PASSED.');
