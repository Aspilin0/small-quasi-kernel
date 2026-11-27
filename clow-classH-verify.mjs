import assert from 'node:assert/strict';
import {
  buildQuasiKernelABC, buildQuasiKernelClassH, computeM, exactLstar, findLemmaA,
  inClassH, inducedAlpha, inspectGPlus, isOriented, isSourcelessSimple,
  selectWitnessClassH, verifyQuasiKernelIndependent,
} from './clow-classH.mjs';

export * from './clow-classH.mjs';

console.log('=== 1. Exhaustive Small-Graph Verification for Class H ===');

{
  let totalChecked = 0;
  for (const n of [3, 4, 5]) {
    const pairs = [];
    for (let i = 0; i < n; ++i) for (let j = i + 1; j < n; ++j) pairs.push([i, j]);
    const adj = Array.from({ length: n }, () => []);
    const indeg = new Int32Array(n);
    function dfs(p) {
      if (p === pairs.length) {
        for (let u = 0; u < n; ++u) if (indeg[u] === 0) return;
        if (!inClassH(adj)) return;
        const { v } = selectWitnessClassH(adj);
        assert.ok(exactLstar(adj, v).gap >= 1);
        const Q = buildQuasiKernelClassH(adj);
        verifyQuasiKernelIndependent(adj, Q);
        ++totalChecked;
        return;
      }
      const [i, j] = pairs[p];
      dfs(p + 1);
      adj[i].push(j); ++indeg[j]; dfs(p + 1); adj[i].pop(); --indeg[j];
      adj[j].push(i); ++indeg[i]; dfs(p + 1); adj[j].pop(); --indeg[i];
    }
    dfs(0);
  }
  // 5-vertex oriented sourceless core orbits + arbitrary 0/1 private/shared sinks in Class H
  const n5 = 5;
  const pairs5 = [];
  for (let i = 0; i < n5; ++i) for (let j = i + 1; j < n5; ++j) pairs5.push([i, j]);
  const perms5 = [];
  (function genP(cur, used) {
    if (cur.length === n5) { perms5.push(cur); return; }
    for (let i = 0; i < n5; ++i) if (!(used & (1 << i))) genP([...cur, i], used | (1 << i));
  })([], 0);
  const seen5 = new Set();
  const core5 = Array.from({ length: n5 }, () => []);
  const indeg5 = new Int32Array(n5);
  let core5Classes = 0, orient5WithSinks = 0, orient5Deg4 = 0;
  function canon5(g) {
    let best = '';
    for (const p of perms5) {
      let s = '';
      for (let u = 0; u < n5; ++u) {
        let mask = 0;
        for (const w of g[p[u]]) mask |= (1 << p.indexOf(w));
        s += mask.toString(32);
      }
      if (!best || s < best) best = s;
    }
    return best;
  }
  function dfs5(p) {
    if (p === pairs5.length) {
      for (let u = 0; u < n5; ++u) if (indeg5[u] === 0 || core5[u].length === 0) return;
      const key = canon5(core5);
      if (seen5.has(key)) return;
      seen5.add(key);
      ++core5Classes;
      const attach = Array(n5).fill(0);
      function dfsSink(u, numSinks) {
        if (u === n5) {
          const adj = Array.from({ length: n5 + numSinks }, (_, i) => i < n5 ? [...core5[i]] : []);
          for (let i = 0; i < n5; ++i) if (attach[i] > 0) adj[i].push(n5 + attach[i] - 1);
          if (!inClassH(adj)) return;
          const { v } = selectWitnessClassH(adj);
          assert.ok(exactLstar(adj, v).gap >= 1);
          const Q = buildQuasiKernelClassH(adj);
          verifyQuasiKernelIndependent(adj, Q);
          ++orient5WithSinks;
          if (adj.some(r => r.length >= 4)) ++orient5Deg4;
          return;
        }
        attach[u] = 0;
        dfsSink(u + 1, numSinks);
        for (let s = 1; s <= numSinks + 1; ++s) {
          attach[u] = s;
          dfsSink(u + 1, Math.max(numSinks, s));
        }
      }
      dfsSink(0, 0);
      return;
    }
    const [i, j] = pairs5[p];
    dfs5(p + 1);
    core5[i].push(j); ++indeg5[j]; dfs5(p + 1); core5[i].pop(); --indeg5[j];
    core5[j].push(i); ++indeg5[i]; dfs5(p + 1); core5[j].pop(); --indeg5[i];
  }
  dfs5(0);
  console.log(`Exhaustive oriented Class H (n=3..5): ${totalChecked} digraphs passed.`);
  console.log(`Exhaustive 5v oriented core orbits (${core5Classes}) + arbitrary 0/1 sinks in Class H: ${orient5WithSinks} digraphs passed (${orient5Deg4} with d+=4).`);
}

{
  const n = 4;
  const pairs = [];
  for (let i = 0; i < n; ++i) for (let j = i + 1; j < n; ++j) pairs.push([i, j]);
  // Orbit representatives under S_4 to keep runtime fast (~1s) while covering ALL isomorphism classes!
  const perms = [];
  (function genPerm(cur, used) {
    if (cur.length === n) { perms.push(cur); return; }
    for (let i = 0; i < n; ++i) if (!(used & (1 << i))) genPerm([...cur, i], used | (1 << i));
  })([], 0);
  const seen = new Set();
  let coreClasses = 0, totalWithSinks = 0, deg4Cases = 0;
  const core = Array.from({ length: n }, () => []);
  const indeg = new Int32Array(n);
  function canon(g) {
    let best = '';
    for (const p of perms) {
      let s = '';
      for (let u = 0; u < n; ++u) {
        let mask = 0;
        for (const w of g[p[u]]) mask |= (1 << p.indexOf(w));
        s += mask.toString(16);
      }
      if (!best || s < best) best = s;
    }
    return best;
  }
  function dfsCore(p) {
    if (p === pairs.length) {
      for (let u = 0; u < n; ++u) if (indeg[u] === 0 || core[u].length === 0) return;
      const key = canon(core);
      if (seen.has(key)) return;
      seen.add(key);
      ++coreClasses;
      // Attach 0 or 1 sink per core vertex (all partitions into shared/private sinks)
      const attach = Array(n).fill(0);
      function dfsSink(u, numSinks) {
        if (u === n) {
          const adj = Array.from({ length: n + numSinks }, (_, i) => i < n ? [...core[i]] : []);
          for (let i = 0; i < n; ++i) if (attach[i] > 0) adj[i].push(n + attach[i] - 1);
          if (!inClassH(adj)) return;
          const { v } = selectWitnessClassH(adj);
          assert.ok(exactLstar(adj, v).gap >= 1);
          const Q = buildQuasiKernelClassH(adj);
          verifyQuasiKernelIndependent(adj, Q);
          ++totalWithSinks;
          if (adj.some(r => r.length >= 4)) ++deg4Cases;
          return;
        }
        attach[u] = 0;
        dfsSink(u + 1, numSinks);
        for (let s = 1; s <= numSinks + 1; ++s) {
          attach[u] = s;
          dfsSink(u + 1, Math.max(numSinks, s));
        }
      }
      dfsSink(0, 0);
      return;
    }
    const [i, j] = pairs[p];
    dfsCore(p + 1);
    core[i].push(j); ++indeg[j]; dfsCore(p + 1); core[i].pop(); --indeg[j];
    core[j].push(i); ++indeg[i]; dfsCore(p + 1); core[j].pop(); --indeg[i];
    core[i].push(j); core[j].push(i); ++indeg[i]; ++indeg[j]; dfsCore(p + 1);
    core[i].pop(); core[j].pop(); --indeg[i]; --indeg[j];
  }
  dfsCore(0);
  console.log(`Exhaustive 4v general core orbits (${coreClasses}) + arbitrary 0/1 sinks in Class H: ${totalWithSinks} digraphs passed (${deg4Cases} with d+=4).`);
}

console.log('\n=== 2. Diverse & Adversarial Class H Verification ===');

// Explicit tight Class H instances on the boundary d+(u) + alpha(u) = 6:
{
  const tightCases = [
    // K_3^* + 6 leaves (9v, d+=4, alpha=2, M=2)
    ['K_3^* + 6 leaves (9v)', [[1,2,3,4],[0,2,5,6],[0,1,7,8],[1,2],[1,2],[0,2],[0,2],[0,1],[0,1]]],
    // K_3^* + 3 leaves + 3 sinks (9v, d+=4, alpha=2, M=2, k=1)
    ['K_3^* + 3 leaves + 3 sinks (9v)', [[1,2,3,4],[0,2,5,6],[0,1,7,8],[1,2],[],[0,2],[],[0,1],[]]],
    // T_5 + 10 leaves (15v, oriented, d+=4, alpha=2, M=2)
    ['T_5 + 10 leaves (15v)', Array.from({ length: 15 }, (_, i) => i < 5
      ? [(i + 1) % 5, (i + 2) % 5, 5 + 2 * i, 6 + 2 * i]
      : [(((i - 5) >> 1) + 1) % 5, (((i - 5) >> 1) + 2) % 5])],
    // QR_7 + 7 private sinks (14v, oriented, d+=4, alpha=2, M=1, no two disjoint QKs!)
    ['QR_7 + 7 sinks (14v)', Array.from({ length: 14 }, (_, i) => i < 7
      ? [(i + 1) % 7, (i + 2) % 7, (i + 4) % 7, 7 + i] : [])],
    // K_4^* + 4 leaves + 4 sinks (12v, hybrid (4,1) + (4,2), M=1)
    ['K_4^* + 4 leaves + 4 sinks (12v)', Array.from({ length: 12 }, (_, i) => i < 4
      ? [0,1,2,3].filter(j => j !== i).concat([4 + i])
      : (i < 8 ? [0,1,2,3].filter(j => j !== (i - 4)).concat([4 + i]) : []))],
  ];
  for (const [name, adj] of tightCases) {
    assert.ok(isSourcelessSimple(adj) && inClassH(adj), `${name} not in Class H`);
    const res = selectWitnessClassH(adj);
    assert.ok(exactLstar(adj, res.v).gap >= 1);
    const Q = buildQuasiKernelClassH(adj);
    verifyQuasiKernelIndependent(adj, Q);
    console.log(`  Tight Class H instance "${name}": witness v=${res.v} (${res.branch}), |Q|=${Q.length}/${adj.length}.`);
  }
}
let seed = 20261127;
const rand = () => { seed = (seed * 1664525 + 1013904223) >>> 0; return seed / 4294967296; };
const randInt = k => Math.floor(rand() * k);

const branchCounts = new Map();
let hybridCount = 0;
for (let t = 0; t < 5000; ++t) {
  const mode = t % 6;
  let adj;
  if (mode === 0) {
    const n = 4 + randInt(14);
    const oriented = rand() < 0.4;
    adj = Array.from({ length: n }, () => []);
    for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n);
    for (let s = 0; s < n * 6; ++s) {
      const u = randInt(n), w = randInt(n);
      if (u === w || adj[u].includes(w) || (oriented && adj[w].includes(u))) continue;
      adj[u].push(w);
      if (!inClassH(adj)) adj[u].pop();
    }
    if (rand() < 0.45) {
      for (let u = 0; u < n; ++u) {
        if (rand() < 0.3) {
          const z = adj.length;
          adj.push([]);
          adj[u].push(z);
          if (!inClassH(adj)) { adj[u].pop(); adj.pop(); }
        }
      }
    }
  } else if (mode === 1) {
    // M = 0 mixed degrees (2,3,4 and high-degree Type I)
    const n = 5 + randInt(11);
    adj = Array.from({ length: n }, () => []);
    for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n, (i + 2) % n);
    for (let s = 0; s < n * 5; ++s) {
      const u = randInt(n), w = randInt(n);
      if (u === w || adj[u].includes(w)) continue;
      adj[u].push(w);
      if (!inClassH(adj)) adj[u].pop();
    }
  } else if (mode === 2) {
    // M = 2 deg-4 rich cores + leaves/sinks
    const m = 3 + randInt(6);
    adj = Array.from({ length: m }, () => []);
    for (let i = 0; i < m; ++i) adj[i].push((i + 1) % m, (i + 2) % m);
    for (let i = 0; i < m; ++i) {
      if (rand() < 0.75) {
        const y1 = adj.length, y2 = adj.length + 1;
        adj.push([], []);
        const coreOut = [...adj[i]];
        adj[i].push(y1, y2);
        adj[y1] = [...coreOut];
        adj[y2] = rand() < 0.5 ? [...coreOut] : [];
        if (rand() < 0.4) { const extra = randInt(m); if (!adj[y1].includes(extra)) adj[y1].push(extra); }
        if (!inClassH(adj)) { adj[i].splice(-2); adj.splice(-2); }
      }
    }
  } else if (mode === 3) {
    // High-degree Type I (d+ up to 11!) + Type II/III attachments
    const m = 6 + randInt(6);
    adj = Array.from({ length: m }, () => []);
    for (let i = 0; i < m; ++i) {
      for (let j = i + 1; j < m; ++j) {
        const r = randInt(3);
        if (r === 0) adj[i].push(j);
        else if (r === 1) adj[j].push(i);
        else { adj[i].push(j); adj[j].push(i); }
      }
    }
    if (!isSourcelessSimple(adj)) continue;
    if (rand() < 0.5) {
      const z = adj.length;
      adj.push([]);
      for (let i = 0; i < m; ++i) adj[i].push(z);
    }
    for (let k = 0; k < 3; ++k) {
      const id = adj.length;
      adj.push([]);
      const p = randInt(m);
      adj[p].push(id);
      for (let c = 0; c < 3; ++c) {
        const target = randInt(m);
        if (!adj[id].includes(target)) adj[id].push(target);
      }
      if (!inClassH(adj)) { adj[p].pop(); adj.pop(); }
    }
  } else if (mode === 4) {
    // M = 3 / Fact-2 k=2 targeted: 3-out + private sinks
    const m = 4 + randInt(6);
    adj = Array.from({ length: m }, () => []);
    for (let i = 0; i < m; ++i) adj[i].push((i + 1) % m);
    for (let u = 0; u < m; ++u) {
      const add = randInt(3);
      for (let s = 0; s < add; ++s) {
        const id = adj.length;
        adj.push([]);
        adj[u].push(id);
        if (rand() < 0.4) adj[id].push((u + 1) % m, (u + 2) % m);
        if (!inClassH(adj)) { adj[u].pop(); adj.pop(); }
      }
    }
  } else {
    // Dense (4,2) general digraphs
    const n = 5 + randInt(11);
    adj = Array.from({ length: n }, () => []);
    for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n, (i + 2) % n);
    for (let s = 0; s < n * 8; ++s) {
      const u = randInt(n), w = randInt(n);
      if (u === w || adj[u].includes(w) || adj[u].length >= 4) continue;
      adj[u].push(w);
      if (!inClassH(adj)) adj[u].pop();
    }
  }
  if (!isSourcelessSimple(adj) || !inClassH(adj)) continue;
  const res = selectWitnessClassH(adj);
  assert.ok(exactLstar(adj, res.v).gap >= 1);
  const Q = buildQuasiKernelClassH(adj);
  verifyQuasiKernelIndependent(adj, Q);
  branchCounts.set(res.branch, (branchCounts.get(res.branch) || 0) + 1);
  ++hybridCount;
}
console.log(`Hybrid Class H verification: ${hybridCount} digraphs passed constructive L*>=1 & independent small QK check.`);
console.log('Proof branches exercised:', Object.fromEntries([...branchCounts.entries()].sort()));

console.log('\n=== 3. Verifying Oriented (4,3) Counterexamples to g>=1 and g+>=1 ===');

function exactMinQuasiKernelOnSinksCore(core, sinks) {
  const m = core.length;
  let best = Infinity, bestJ = null;
  for (let mask = 1; mask < (1 << m); ++mask) {
    let ok = true, sz = 0;
    for (let i = 0; i < m && ok; ++i) {
      if (mask & (1 << i)) {
        ++sz;
        for (const j of core[i]) if (mask & (1 << j)) { ok = false; break; }
      }
    }
    if (!ok) continue;
    const d = new Int8Array(m).fill(3);
    for (let i = 0; i < m; ++i) if (mask & (1 << i)) d[i] = 0;
    for (let i = 0; i < m; ++i) if (d[i] === 0) for (const j of core[i]) {
      if (d[j] > 1) d[j] = 1;
      for (const k of core[j]) if (d[k] > 2) d[k] = 2;
    }
    if (d.some(x => x > 2)) continue;
    let cost = sz;
    for (let i = 0; i < m; ++i) if (d[i] === 2) cost += sinks[i];
    if (cost < best) {
      best = cost;
      bestJ = [];
      for (let i = 0; i < m; ++i) if (mask & (1 << i)) bestJ.push(i);
    }
  }
  return { best, bestJ };
}

for (const [m, expectMaxG, expectMaxGP] of [[3, 0, 1], [4, 0, 0], [5, 0, 0]]) {
  const coreN = 5 + m;
  const core = Array.from({ length: coreN }, () => []);
  const sinks = Array(coreN).fill(0);
  for (let i = 0; i < 5; ++i) {
    core[i] = [(i + 1) % 5, (i + 2) % 5];
    sinks[i] = 2;
  }
  for (let j = 0; j < m; ++j) {
    core[5 + j] = [5 + ((j + 1) % m), j % 5, (j + 1) % 5, (j + 2) % 5];
  }
  const adj = core.map(r => [...r]);
  for (let u = 0; u < coreN; ++u) {
    for (let s = 0; s < sinks[u]; ++s) {
      const id = adj.length;
      adj.push([]);
      adj[u].push(id);
    }
  }
  assert.ok(isSourcelessSimple(adj));
  assert.ok(isOriented(adj));
  assert.equal(Math.max(...adj.map(r => r.length)), 4);
  assert.equal(Math.max(...adj.map(r => inducedAlpha(adj, r))), 3);
  const rows = inspectGPlus(adj);
  assert.equal(Math.max(...rows.map(r => r.g)), expectMaxG);
  assert.equal(Math.max(...rows.map(r => r.gPlus)), expectMaxGP);
  for (let v = 0; v < coreN; ++v) assert.ok(exactLstar(adj, v).gap <= 0);
  const { best, bestJ } = exactMinQuasiKernelOnSinksCore(core, sinks);
  // Build full Q and verify independently via check.mjs
  const d = new Int8Array(coreN).fill(3);
  for (const u of bestJ) d[u] = 0;
  for (const u of bestJ) for (const w of core[u]) if (d[w] > 1) d[w] = 1;
  const fullQ = [...bestJ];
  for (let i = 0; i < 5; ++i) if (d[i] > 1) fullQ.push(coreN + 2 * i, coreN + 2 * i + 1);
  assert.equal(fullQ.length, best);
  verifyQuasiKernelIndependent(adj, fullQ);
  console.log(`Verified oriented (4,3) T_5 + C_${m} + 10 sinks (${adj.length}v): max g=${expectMaxG}, max g+=${expectMaxGP}, L*<=0 everywhere, q(D)=${best}/${adj.length}.`);
}

{
  const core10 = [[2,9,3,1],[3,4],[6,3,7,4],[4,5],[5,6],[9,6],[9,3],[4,1,8,9],[4,0,5,3],[1,3]];
  const sinks10 = [0, 2, 0, 2, 2, 2, 2, 0, 0, 2];
  const adj = core10.map(r => [...r]);
  const sinkStart = [];
  for (let u = 0; u < 10; ++u) {
    sinkStart.push(adj.length);
    for (let s = 0; s < sinks10[u]; ++s) { const id = adj.length; adj.push([]); adj[u].push(id); }
  }
  assert.ok(isSourcelessSimple(adj) && isOriented(adj));
  assert.equal(Math.max(...adj.map(r => r.length)), 4);
  assert.equal(Math.max(...adj.map(r => inducedAlpha(adj, r))), 3);
  const rows = inspectGPlus(adj);
  assert.equal(Math.max(...rows.map(r => r.g)), 0);
  assert.equal(Math.max(...rows.map(r => r.gPlus)), 0);
  assert.equal(rows.filter(r => r.gPlus === -1).length, 4);
  const { best, bestJ } = exactMinQuasiKernelOnSinksCore(core10, sinks10);
  const d = new Int8Array(10).fill(3);
  for (const u of bestJ) d[u] = 0;
  for (const u of bestJ) for (const w of core10[u]) if (d[w] > 1) d[w] = 1;
  const fullQ = [...bestJ];
  for (let u = 0; u < 10; ++u) if (d[u] > 1) for (let s = 0; s < sinks10[u]; ++s) fullQ.push(sinkStart[u] + s);
  assert.equal(fullQ.length, best);
  verifyQuasiKernelIndependent(adj, fullQ);
  console.log(`Verified 22v oriented (4,3) counterexample: 4 core vertices g=g+=-1, rest 0, q(D)=${best}/22.`);
}

console.log('\n=== 4. Verifying M=1 alpha+=2 Obstruction, Lemma B/C, and (d-1)/d Bound ===');

for (const r of [4, 5, 6]) {
  const m = 2 * r;
  const adj = Array.from({ length: 5 * r }, () => []);
  // 0..m-1: K_{2r}^*; m..2m-1: private sinks; 2m..2m+r-1: pair-vertices s_k
  for (let i = 0; i < m; ++i) {
    const rest = Array.from({ length: m }, (_, j) => j).filter(j => j !== i);
    const pairV = 2 * m + (i >> 1);
    adj[i] = [...rest, m + i, pairV];
  }
  for (let k = 0; k < r; ++k) {
    adj[2 * m + k] = Array.from({ length: m }, (_, j) => j);
  }
  assert.ok(isSourcelessSimple(adj));
  assert.equal(Math.max(...adj.map(row => inducedAlpha(adj, row))), 2);
  assert.equal(computeM(adj).M, 1);
  const rows = inspectGPlus(adj);
  for (let i = 0; i < m; ++i) {
    assert.equal(rows[i].g, 4 - r);
    assert.equal(rows[i].gPlus, 5 - r);
  }
  for (let k = 0; k < r; ++k) {
    assert.equal(rows[2 * m + k].g, 1 - r);
    assert.equal(rows[2 * m + k].gPlus, 1 - r);
  }
  // Verify Lemma C solves it with |Q| = 1 (and Lemma A0 also solves it!)
  const resC = buildQuasiKernelABC(adj, { allowA: false, allowB: false, allowC: true });
  verifyQuasiKernelIndependent(adj, resC.Q);
  assert.equal(resC.Q.length, 1);
  const resA = buildQuasiKernelABC(adj, { allowA: true, allowB: false, allowC: false });
  verifyQuasiKernelIndependent(adj, resA.Q);
  console.log(`Verified M=1 alpha+=2 K_${m}^* + ${m} sinks + ${r} pairs (${5 * r}v): core g=${4 - r}, g+=${5 - r}, pair g=g+=${1 - r}; Lemma C => |Q|=${resC.Q.length}/${5 * r}.`);
}

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
  assert.equal(findLemmaA(adj), null);
  const { Q, usedRules } = buildQuasiKernelABC(adj, { allowA: true, allowB: true, allowC: false });
  verifyQuasiKernelIndependent(adj, Q);
  console.log(`Verified Lemma B solves Lemma-A-irreducible CP_8^* + 16 leaves (24v): rules=${JSON.stringify(usedRules)}, |Q|=${Q.length}/24.`);
}

{
  let checked = 0;
  for (const d of [2, 3, 4]) {
    const k = d - 1;
    for (let t = 0; t < 400; ++t) {
      const n = 5 + randInt(10);
      const adj = Array.from({ length: n }, () => []);
      for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n);
      for (let s = 0; s < n * 5; ++s) {
        const u = randInt(n), w = randInt(n);
        if (u === w || adj[u].includes(w)) continue;
        adj[u].push(w);
        if (inducedAlpha(adj, adj[u]) > k) adj[u].pop();
      }
      const allV = Array.from({ length: n }, (_, i) => i);
      const alphaG = inducedAlpha(adj, allV);
      assert.ok(d * alphaG <= (d - 1) * n, `Bound violated: d=${d}, alpha=${alphaG}, n=${n}`);
      ++checked;
    }
  }
  console.log(`Verified universal alpha(D) <= ((d-1)/d)n bound on ${checked} sourceless general digraphs (d=2,3,4).`);
}

console.log('\nALL CLASS H & COUNTEREXAMPLE VERIFICATIONS PASSED!');
