import assert from 'node:assert/strict';
import { verifySmallQuasiKernel } from './check.mjs';
import { exactLstar as enumerateLstar, findLemmaA, inducedAlpha, inspectGPlus, isOriented } from './clow-local.mjs';

export { inducedAlpha, inspectGPlus, isOriented, verifySmallQuasiKernel };

export function exactLstar(adj, v) {
  if (adj[v].length === 0) return { gap: 0, F: [], S: [] };
  return enumerateLstar(adj, v);
}

export function maxOutAlpha(adj) {
  let mx = 0;
  for (let u = 0; u < adj.length; ++u) {
    const a = inducedAlpha(adj, adj[u]);
    if (a > mx) mx = a;
  }
  return mx;
}

export function findLemmaAReduction(adj) {
  const reduction = findLemmaA(adj);
  if (reduction === null) return null;
  const { y, u, kind } = reduction;
  return { y, u, kind: kind === 'A0' ? 'A0_bidirected_in' : 'A1_subsumed_child' };
}

// Constructive 1-step witness selector for locally out-semicomplete digraphs (alpha+(D) <= 1).
export function selectWitnessAlpha1(adj) {
  const n = adj.length;
  const core = [];
  let sinkParent = -1;
  for (let u = 0; u < n; ++u) {
    if (adj[u].length > 0) {
      core.push(u);
      if (adj[u].some(w => adj[w].length === 0) && sinkParent === -1) sinkParent = u;
    }
  }
  assert.ok(core.length > 0);
  if (sinkParent !== -1) {
    assert.ok(exactLstar(adj, sinkParent).gap >= 1);
    return { v: sinkParent, root: sinkParent, steps: 0 };
  }
  let r = core[0];
  for (const u of core) if (adj[u].length < adj[r].length) r = u;
  for (const cand of [r, ...adj[r]]) {
    if (adj[cand].length > 0 && exactLstar(adj, cand).gap >= 1) {
      return { v: cand, root: r, steps: cand === r ? 0 : 1 };
    }
  }
  throw new Error('Alpha<=1 witness selection failed');
}

// Constructive 1-step witness selector for alpha+(D) <= 2 with M = 0 (e.g. min in-degree >= 2).
export function selectWitnessAlpha2M0(adj) {
  const n = adj.length;
  const indeg = new Int32Array(n);
  for (let u = 0; u < n; ++u) for (const w of adj[u]) ++indeg[w];
  const inI1 = indeg.map(d => d === 1);
  const inZ = adj.map(row => row.every(w => !inI1[w]));
  for (let u = 0; u < n; ++u) {
    for (const w of adj[u]) assert.ok(!(inI1[w] && inZ[w]), 'Expected M = 0');
  }
  const core = [];
  let sinkParent = -1;
  for (let u = 0; u < n; ++u) {
    if (adj[u].length > 0) {
      core.push(u);
      if (adj[u].some(w => adj[w].length === 0) && sinkParent === -1) sinkParent = u;
    }
  }
  if (sinkParent !== -1) {
    assert.ok(exactLstar(adj, sinkParent).gap >= 1);
    return { v: sinkParent, root: sinkParent, steps: 0 };
  }
  let r = core[0];
  for (const u of core) if (adj[u].length < adj[r].length) r = u;
  for (const cand of [r, ...adj[r]]) {
    if (adj[cand].length > 0 && exactLstar(adj, cand).gap >= 1) {
      return { v: cand, root: r, steps: cand === r ? 0 : 1 };
    }
  }
  throw new Error('Alpha<=2 M=0 witness selection failed');
}

// General Small Quasi-Kernel solver combining Source rule, Lemma A reduction, and g+(v) >= 1 step!
export function buildQuasiKernelEnhanced(adj) {
  function solve(verts, preCovered) {
    if (verts.length === 0) return [];
    const idxMap = new Map(verts.map((u, i) => [u, i]));
    const subAdj = verts.map(u => adj[u].filter(w => idxMap.has(w)).map(w => idxMap.get(w)));
    const m = verts.length;
    const indeg = new Int32Array(m);
    for (let i = 0; i < m; ++i) for (const j of subAdj[i]) ++indeg[j];
    for (let r = 0; r < m; ++r) {
      if (indeg[r] === 0) {
        assert.ok(preCovered.has(verts[r]));
        if (subAdj[r].length === 0) {
          const nextP = new Set(preCovered);
          nextP.delete(verts[r]);
          return solve(verts.filter((_, i) => i !== r), nextP);
        }
        const del = new Uint8Array(m);
        del[r] = 1;
        for (const a of subAdj[r]) del[a] = 1;
        const nextVerts = [], hasParent = new Uint8Array(m);
        for (let i = 0; i < m; ++i) if (!del[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasParent[j] = 1; }
        const nextP = new Set();
        for (let i = 0; i < m; ++i) if (!del[i] && (preCovered.has(verts[i]) || !hasParent[i])) nextP.add(verts[i]);
        return [verts[r], ...solve(nextVerts, nextP)];
      }
    }

    const red = findLemmaAReduction(subAdj);
    if (red !== null) {
      const { y, u } = red;
      const del = new Uint8Array(m);
      del[y] = 1;
      for (const a of subAdj[y]) del[a] = 1;
      const nextVerts = [], hasParent = new Uint8Array(m);
      for (let i = 0; i < m; ++i) if (!del[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasParent[j] = 1; }
      const nextP = new Set();
      for (let i = 0; i < m; ++i) if (!del[i] && (preCovered.has(verts[i]) || !hasParent[i])) nextP.add(verts[i]);
      const Qp = solve(nextVerts, nextP);
      if (u !== null && Qp.includes(verts[u])) return Qp;
      return [verts[y], ...Qp];
    }

    const rows = inspectGPlus(subAdj);
    const hit = rows.find(r => subAdj[r.v].length > 0 && r.gPlus >= 1);
    assert.ok(hit !== undefined, 'No Lemma A reduction and no g+(v) >= 1 vertex found');
    const v = hit.v;
    const S = hit.S;
    const delU = new Uint8Array(m);
    delU[v] = 1;
    for (const a of subAdj[v]) delU[a] = 1;
    for (const s of S) { delU[s] = 1; for (const w of subAdj[s]) delU[w] = 1; }
    const nextVerts = [], hasParentU = new Uint8Array(m);
    for (let i = 0; i < m; ++i) if (!delU[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasParentU[j] = 1; }
    const nextP = new Set();
    for (let i = 0; i < m; ++i) if (!delU[i] && (preCovered.has(verts[i]) || !hasParentU[i])) nextP.add(verts[i]);
    const Qp = solve(nextVerts, nextP);
    const qHitsV = Qp.some(q => adj[q].includes(verts[v]));
    const globalS = S.map(s => verts[s]);
    return (hit.sHitsV || qHitsV) ? [...globalS, ...Qp] : [verts[v], ...globalS, ...Qp];
  }
  return solve(adj.map((_, i) => i), new Set());
}

// 1. Verify Sharp Boundary Counterexamples to Local Inequalities

// (1a) Oriented K_{1,4}-free (21v: QR_7 + 14 private sinks): d+=5, alpha+=3, g <= 0 & g+ <= 0 everywhere!
{
  const qr7Sinks = Array.from({ length: 21 }, () => []);
  for (let i = 0; i < 7; ++i) {
    qr7Sinks[i] = [(i + 1) % 7, (i + 2) % 7, (i + 4) % 7, 7 + 2 * i, 8 + 2 * i];
  }
  assert.ok(isOriented(qr7Sinks));
  assert.equal(maxOutAlpha(qr7Sinks), 3);
  const rows = inspectGPlus(qr7Sinks);
  assert.ok(rows.slice(0, 7).every(r => r.g === -1 && r.gPlus === -1));
  assert.ok(rows.slice(7).every(r => r.g === 0 && r.gPlus === 0));
  console.log('Verified (5,3) oriented counterexample: QR_7 + 14 sinks (21v), core g = g+ = -1, sinks 0.');
}

// (1b) Oriented (4,3) L* = 0 boundary (15v: T_5 + 10 private sinks): L*(v) = 0 everywhere, while core g(v) = 3!
{
  const t5Sinks = Array.from({ length: 15 }, () => []);
  for (let i = 0; i < 5; ++i) t5Sinks[i] = [(i + 1) % 5, (i + 2) % 5, 5 + 2 * i, 6 + 2 * i];
  assert.ok(isOriented(t5Sinks));
  assert.equal(Math.max(...t5Sinks.map(r => r.length)), 4);
  assert.equal(maxOutAlpha(t5Sinks), 3);
  for (let v = 0; v < 5; ++v) assert.equal(exactLstar(t5Sinks, v).gap, 0);
  const rows = inspectGPlus(t5Sinks);
  assert.ok(rows.slice(0, 5).every(r => r.g === 3));
  console.log('Verified (4,3) oriented L*=0 boundary: T_5 + 10 sinks (15v), L*(v)=0 everywhere, core g(v)=3.');
}

// (1c) 2-cycle (4,3) counterexample (9v: K_3^* + 6 private sinks): d+=4, alpha+=3, g = g+ = L* = 0 everywhere!
{
  const k3Sinks = Array.from({ length: 9 }, () => []);
  for (let i = 0; i < 3; ++i) {
    k3Sinks[i] = [[1, 2], [0, 2], [0, 1]][i].concat([3 + 2 * i, 4 + 2 * i]);
  }
  assert.equal(Math.max(...k3Sinks.map(r => r.length)), 4);
  assert.equal(maxOutAlpha(k3Sinks), 3);
  const rows = inspectGPlus(k3Sinks);
  assert.ok(rows.every(r => r.g === 0 && r.gPlus === 0));
  console.log('Verified (4,3) 2-cycle counterexample: K_3^* + 6 sinks (9v), g = g+ = 0 everywhere.');
}

// (1d) 2-cycle alpha+ = 2 counterexamples: K_m^* + 2m leaves (m=4,5,6) — AND solved by Lemma A!
for (const [m, expCoreG, expCoreGP, expLeafG] of [[4, 0, 1, -2], [5, -1, 0, -3], [6, -2, -1, -4]]) {
  const adj = Array.from({ length: 3 * m }, () => []);
  for (let i = 0; i < m; ++i) {
    const rest = Array.from({ length: m }, (_, j) => j).filter(j => j !== i);
    adj[i] = [...rest, m + 2 * i, m + 2 * i + 1];
    adj[m + 2 * i] = [...rest];
    adj[m + 2 * i + 1] = [...rest];
  }
  assert.equal(maxOutAlpha(adj), 2);
  const rows = inspectGPlus(adj);
  assert.ok(rows.slice(0, m).every(r => r.g === expCoreG && r.gPlus === expCoreGP));
  assert.ok(rows.slice(m).every(r => r.g === expLeafG && r.gPlus === expLeafG));
  const Q = buildQuasiKernelEnhanced(adj);
  verifySmallQuasiKernel(adj, Q);
  console.log(`Verified (${m + 1},2) 2-cycle K_${m}^* + ${2 * m} leaves (${3 * m}v): core g=${expCoreG}, g+=${expCoreGP}, leaf g=${expLeafG}; Lemma A => |Q|=${Q.length}/${3 * m}.`);
}

// (1e) Lemma-A-irreducible 2-cycle alpha+ = 2 counterexample: CocktailParty CP_8^* + 16 leaves (24v)!
{
  const m = 8;
  const adj = Array.from({ length: 3 * m }, () => []);
  for (let i = 0; i < m; ++i) {
    const partner = i ^ 1;
    const outC = Array.from({ length: m }, (_, j) => j).filter(j => j !== i && j !== partner);
    const allExceptI = Array.from({ length: m }, (_, j) => j).filter(j => j !== i);
    adj[i] = [...outC, m + 2 * i, m + 2 * i + 1];
    adj[m + 2 * i] = [...allExceptI];
    adj[m + 2 * i + 1] = [...allExceptI];
  }
  assert.equal(maxOutAlpha(adj), 2);
  assert.equal(findLemmaAReduction(adj), null);
  const rows = inspectGPlus(adj);
  assert.ok(rows.every(r => r.g <= -2 && r.gPlus <= -1));
  console.log('Verified Lemma-A-irreducible alpha+=2 counterexample: CP_8^* + 16 leaves (24v), all g <= -2, g+ <= -1.');
}

// (1f) Verify SSNC blowup functor Phi(H) = H[QR_7] + 2 leaves/v on H = T_3 (63v) and H = C_7(1,2) (147v):
for (const [name, H] of [
  ['T_3', [[1], [2], [0]]],
  ['C_7(1,2)', Array.from({ length: 7 }, (_, i) => [(i + 1) % 7, (i + 2) % 7])],
]) {
  const m = H.length, coreN = 7 * m;
  const adj = Array.from({ length: 3 * coreN }, () => []);
  const qr = [1, 2, 4];
  for (let i = 0; i < m; ++i) {
    for (let c = 0; c < 7; ++c) {
      const u = 7 * i + c;
      const outC = qr.map(q => 7 * i + ((c + q) % 7));
      for (const j of H[i]) for (let c2 = 0; c2 < 7; ++c2) outC.push(7 * j + c2);
      adj[u] = [...outC, coreN + 2 * u, coreN + 2 * u + 1];
      adj[coreN + 2 * u] = [...outC];
      adj[coreN + 2 * u + 1] = [...outC];
    }
  }
  assert.ok(isOriented(adj));
  assert.equal(maxOutAlpha(adj), 2);
  const rows = inspectGPlus(adj);
  for (let i = 0; i < m; ++i) {
    const n1 = new Set(H[i]);
    const n2 = new Set();
    for (const j of H[i]) for (const k of H[j]) if (k !== i && !n1.has(k)) n2.add(k);
    const diff = n2.size - H[i].length;
    for (let c = 0; c < 7; ++c) {
      const u = 7 * i + c;
      assert.equal(rows[u].g, 2 + 7 * diff);
      assert.equal(rows[coreN + 2 * u].g, 7 * diff);
      assert.equal(rows[coreN + 2 * u + 1].g, 7 * diff);
    }
  }
  const Q = buildQuasiKernelEnhanced(adj);
  verifySmallQuasiKernel(adj, Q);
  console.log(`Verified oriented K_{1,3}-free SSNC functor Phi(${name}) (${adj.length}v): exact formula holds, Lemma A => |Q|=${Q.length}/${adj.length}.`);
}

// 2. Verify Positive Theorems: alpha+(D) <= 1, alpha+(D) <= 2 (M=0), and Class H
let rng = 20261127;
const rand = () => { rng = (rng * 1664525 + 1013904223) >>> 0; return rng / 4294967296; };
const randInt = k => Math.floor(rand() * k);

let alpha1Checked = 0;
for (let t = 0; t < 1000; ++t) {
  const coreN = 3 + randInt(14);
  const adj = Array.from({ length: coreN }, () => []);
  for (let i = 0; i < coreN; ++i) adj[i].push((i + 1) % coreN);
  for (let i = 0; i < coreN; ++i) {
    for (let j = i + 1; j < coreN; ++j) {
      if (adj[i].includes(j) || adj[j].includes(i)) continue;
      const mode = randInt(3);
      if (mode === 0) adj[i].push(j);
      else if (mode === 1) adj[j].push(i);
      else { adj[i].push(j); adj[j].push(i); }
    }
  }
  if (t % 3 === 0) {
    const z = adj.length;
    adj.push([]);
    for (let u = 0; u < coreN; ++u) adj[u].push(z);
  }
  assert.equal(maxOutAlpha(adj), 1);
  const { v } = selectWitnessAlpha1(adj);
  assert.ok(exactLstar(adj, v).gap >= 1);
  const Q = buildQuasiKernelEnhanced(adj);
  verifySmallQuasiKernel(adj, Q);
  ++alpha1Checked;
}
console.log(`Verified Theorem (alpha+ <= 1): ${alpha1Checked} general digraphs passed 1-step L*(v)>=1 & small quasi-kernel check.`);

let alpha2M0Checked = 0;
for (let t = 0; t < 1200; ++t) {
  const n = 5 + randInt(13);
  const adj = Array.from({ length: n }, () => []);
  for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n, (i + 2) % n);
  for (let s = 0; s < n * 4; ++s) {
    const u = randInt(n), w = randInt(n);
    if (u === w || adj[u].includes(w)) continue;
    if (t % 2 === 0 && adj[w].includes(u)) continue;
    adj[u].push(w);
    if (inducedAlpha(adj, adj[u]) > 2) adj[u].pop();
  }
  if (maxOutAlpha(adj) > 2) continue;
  const { v } = selectWitnessAlpha2M0(adj);
  assert.ok(exactLstar(adj, v).gap >= 1);
  const Q = buildQuasiKernelEnhanced(adj);
  verifySmallQuasiKernel(adj, Q);
  ++alpha2M0Checked;
}
console.log(`Verified Theorem (alpha+ <= 2, M = 0): ${alpha2M0Checked} general digraphs passed 1-step L*(v)>=1 & small quasi-kernel check.`);

let classHChecked = 0;
for (let t = 0; t < 1000; ++t) {
  const n = 5 + randInt(12);
  const oriented = t % 2 === 0;
  const adj = Array.from({ length: n }, () => []);
  for (let i = 0; i < n; ++i) adj[(i + 1) % n].push(i);
  for (let s = 0; s < n * 6; ++s) {
    const u = randInt(n), w = randInt(n);
    if (u === w || adj[u].includes(w) || (oriented && adj[w].includes(u))) continue;
    adj[u].push(w);
    const d = adj[u].length, a = inducedAlpha(adj, adj[u]);
    if (a > 1 && d + a > 6) adj[u].pop();
  }
  if (t % 4 === 0) {
    for (let u = 0; u < n; ++u) {
      if (adj[u].length < 4 && rand() < 0.35) {
        const z = adj.length;
        adj.push([]);
        adj[u].push(z);
        const d = adj[u].length, a = inducedAlpha(adj, adj[u]);
        if (a > 1 && d + a > 6) { adj[u].pop(); adj.pop(); }
      }
    }
  }
  let bestLs = -Infinity;
  for (let v = 0; v < adj.length; ++v) {
    if (adj[v].length > 0) bestLs = Math.max(bestLs, exactLstar(adj, v).gap);
  }
  assert.ok(bestLs >= 1, `Class H graph had max L* = ${bestLs}`);
  const Q = buildQuasiKernelEnhanced(adj);
  verifySmallQuasiKernel(adj, Q);
  ++classHChecked;
}
console.log(`Verified Class H (alpha<=1 or d+alpha<=6): ${classHChecked} hybrid digraphs all satisfied max L*(v)>=1 & 2|Q|<=|V|.`);
