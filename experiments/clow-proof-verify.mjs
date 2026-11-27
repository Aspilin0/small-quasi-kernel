import assert from 'node:assert/strict';
import { allCores, attachments, indices, orbitFilter, size } from './shared/clow-cores.mjs';
import { inspect } from './shared/clow-check.mjs';
import { checkRealizations } from './shared/clow-minima.mjs';
import { verifySmallQuasiKernel } from './shared/check.mjs';
import { exactLstar as enumerateLstar, sourcesAfterDeletingClosedOut } from './shared/clow-local.mjs';

export { verifySmallQuasiKernel };

// At maximum out-degree 3, the source set has at most nine vertices.
export function exactLstar(adj, v) {
  return enumerateLstar(adj, v, 9);
}

// Independent validator for a general sourceless simple digraph (2-cycles allowed, no self-loops).
export function inspectGeneral(adj, degreeLimit = 3) {
  const n = adj.length;
  assert.ok(n > 0);
  const indeg = new Int32Array(n);
  for (let u = 0; u < n; ++u) {
    assert.ok(adj[u].length <= degreeLimit && new Set(adj[u]).size === adj[u].length);
    for (const w of adj[u]) {
      assert.ok(Number.isInteger(w) && w >= 0 && w < n && w !== u);
      ++indeg[w];
    }
  }
  for (let u = 0; u < n; ++u) assert.ok(indeg[u] >= 1, `Vertex ${u} is a source`);
  return adj.map((row, v) => {
    const S = sourcesAfterDeletingClosedOut(adj, v);
    const E = new Set(row);
    for (const s of S) for (const w of adj[s]) E.add(w);
    return { v, S, E: [...E], gap: E.size - S.length };
  });
}

// Constructive witness selection following Theorem 1 case by case.
// Works for all sourceless simple digraphs (2-cycles allowed, max out-deg <= 3).
// When orientedOnly=true, strictly enforces the distance <= 1 bound ({r} U A_C(r)).
export function selectWitness(adj, { orientedOnly = false } = {}) {
  const n = adj.length;
  const isCore = adj.map(row => row.length > 0);
  const coreVerts = [];
  let hasSink = false;
  for (let u = 0; u < n; ++u) {
    if (isCore[u]) coreVerts.push(u);
    else hasSink = true;
  }
  assert.ok(coreVerts.length > 0, 'Non-empty sourceless digraph must have a non-sink');

  for (const v of coreVerts) if (adj[v].every(w => !isCore[w])) return { v, branch: 'F2_only_sinks' };
  for (const v of coreVerts) {
    if (adj[v].filter(w => !isCore[w]).length >= 2) {
      if (exactLstar(adj, v).gap >= 1) return { v, branch: 'F2_two_sinks_v' };
      return { v: adj[v].find(x => isCore[x]), branch: 'F2_two_sinks_w' };
    }
  }

  const indeg = new Int32Array(n);
  for (const u of coreVerts) for (const w of adj[u]) ++indeg[w];
  const inI1 = indeg.map(d => d === 1);
  const inZ = adj.map(row => row.every(w => !inI1[w]));
  let M = -1, uStar = -1;
  for (const u of coreVerts) {
    let c = 0;
    for (const w of adj[u]) if (inI1[w] && inZ[w]) ++c;
    if (c > M) { M = c; uStar = u; }
  }

  const pickIn = (cands, tag) => {
    const seen = new Set();
    for (const v of cands) {
      if (!isCore[v] || seen.has(v)) continue;
      seen.add(v);
      if (exactLstar(adj, v).gap >= 1) return { v, branch: tag };
    }
    throw new Error(`Proof invariant violated in ${tag}`);
  };
  const ball1 = r => [r, ...adj[r]];
  const ball2 = r => {
    const out = [r, ...adj[r]];
    for (const a of adj[r]) if (isCore[a]) out.push(...adj[a]);
    return out;
  };
  const scope = orientedOnly ? ball1 : ball2;

  if (M === 0) {
    if (hasSink) {
      const w = coreVerts.find(u => adj[u].some(x => !isCore[x]));
      return pickIn(orientedOnly ? [w] : ball1(w), 'M0_sink');
    }
    if (orientedOnly) {
      let best = coreVerts[0];
      for (const v of coreVerts) if (adj[v].length < adj[best].length) best = v;
      return pickIn([best], 'M0_sf_oriented');
    }
    const d1 = coreVerts.find(u => adj[u].length === 1);
    if (d1 !== undefined) return pickIn([d1], 'M0_sf_d1');
    const d2 = coreVerts.find(u => adj[u].length === 2);
    if (d2 !== undefined) return pickIn(ball1(d2), 'M0_sf_d2');
    return pickIn(ball2(coreVerts[0]), 'M0_sf_3reg');
  }
  if (M === 3) return pickIn(ball1(uStar), 'M3');
  if (M === 2) return pickIn(scope(uStar), 'M2');

  assert.equal(M, 1);
  if (hasSink) {
    const w = coreVerts.find(u => adj[u].some(x => !isCore[x]));
    return pickIn(ball1(w), 'M1_sink');
  }
  const d1 = coreVerts.find(u => adj[u].length === 1);
  if (d1 !== undefined) return pickIn(orientedOnly ? [d1] : ball2(d1), 'M1_sf_d1');
  const d2 = coreVerts.find(u => adj[u].length === 2);
  if (d2 !== undefined) return pickIn(scope(d2), 'M1_sf_d2');
  return pickIn(scope(coreVerts[0]), 'M1_sf_3reg');
}

// Constructive Small Quasi-Kernel builder implementing Theorem 2 (P(H, P)).
export function buildSmallQuasiKernel(adj) {
  function solve(verts, preCovered) {
    if (verts.length === 0) return [];
    const idxMap = new Map(verts.map((u, i) => [u, i]));
    const subAdj = verts.map(u => adj[u].filter(w => idxMap.has(w)).map(w => idxMap.get(w)));
    const m = verts.length;
    const indeg = new Int32Array(m);
    for (let i = 0; i < m; ++i) for (const j of subAdj[i]) ++indeg[j];
    const sources = [];
    for (let i = 0; i < m; ++i) if (indeg[i] === 0) sources.push(i);

    if (sources.length > 0) {
      const r = sources[0];
      assert.ok(preCovered.has(verts[r]), 'Every source of H must lie in P');
      if (subAdj[r].length === 0) {
        const nextVerts = verts.filter((_, i) => i !== r);
        const nextP = new Set(preCovered);
        nextP.delete(verts[r]);
        return solve(nextVerts, nextP);
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

    const { v } = selectWitness(subAdj);
    const delV = new Uint8Array(m);
    delV[v] = 1;
    for (const a of subAdj[v]) delV[a] = 1;
    const hasParentV = new Uint8Array(m);
    for (let i = 0; i < m; ++i) if (!delV[i]) for (const j of subAdj[i]) hasParentV[j] = 1;
    const S = [];
    for (let i = 0; i < m; ++i) if (!delV[i] && !hasParentV[i]) S.push(i);

    const delU = new Uint8Array(m);
    delU[v] = 1;
    for (const a of subAdj[v]) delU[a] = 1;
    for (const s of S) { delU[s] = 1; for (const w of subAdj[s]) delU[w] = 1; }
    const nextVerts = [], hasParentU = new Uint8Array(m);
    for (let i = 0; i < m; ++i) if (!delU[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasParentU[j] = 1; }
    const nextP = new Set();
    for (let i = 0; i < m; ++i) if (!delU[i] && (preCovered.has(verts[i]) || !hasParentU[i])) nextP.add(verts[i]);
    const Qp = solve(nextVerts, nextP);
    const sHitsV = S.some(s => subAdj[s].includes(v));
    const qHitsV = Qp.some(q => adj[q].includes(verts[v]));
    const globalS = S.map(s => verts[s]);
    return (sHitsV || qHitsV) ? [...globalS, ...Qp] : [verts[v], ...globalS, ...Qp];
  }
  return solve(adj.map((_, i) => i), new Set());
}

function addTournamentHub(adj, extraOut) {
  const t = adj.length;
  for (let i = 0; i < 5; ++i) {
    const row = [t + ((i + 1) % 5), t + ((i + 2) % 5)];
    if (extraOut[i] !== undefined) row.push(extraOut[i]);
    adj.push(row);
  }
}

// 1. Tight boundary instances (both oriented and 2-cycle digraphs).
const tightCases = [];
{
  const g = [[1,2,3],[4,5,6],[4,5,7],[6,7,8],[8],[8],[8],[],[0,9,10]];
  addTournamentHub(g, [0,0,8,8]);
  tightCases.push({ name: 'oriented_M3_child', adj: g, oriented: true });
}
{
  const g = [[1,2,3],[4,5,7],[4,5,7],[6,8],[3],[3],[]];
  addTournamentHub(g, [0,0,0]);
  tightCases.push({ name: 'oriented_M2_child', adj: g, oriented: true });
}
{
  const g = [[1,2,5],[3,6,7],[4,6,7],[2],[1],[],[]];
  addTournamentHub(g, [5,0,0]);
  tightCases.push({ name: 'oriented_M1_shared_sink', adj: g, oriented: true });
}
{
  const twoSink = [[1,2,3],[4,5,6],[],[],[2],[2],[3],[8,0],[9,0],[7,0]];
  assert.equal(exactLstar(twoSink, 0).gap, 0);
  assert.ok(exactLstar(twoSink, 1).gap >= 1);
  tightCases.push({ name: 'oriented_two_sinks_boundary', adj: twoSink, oriented: true });
}
{
  const cycle9 = [[1,5],[2,3,4],[0],[0],[0],[],[7,0,1],[8,0,1],[6,0,1]];
  tightCases.push({ name: 'oriented_clow_cycle_m3', adj: cycle9, oriented: true });
}
{
  const conflict14 = [[1,5,6],[2,3],[4,7],[4,8],[0,9],[10,11],[12,13],[],[],[],[1],[],[1],[]];
  tightCases.push({ name: 'oriented_conflict_14', adj: conflict14, oriented: true });
}
{
  const tight14 = [[1,2,6],[3,4,7],[3,4,8],[5],[5],[9],[],[],[],[10,11,0],[11,12,0],[12,13,1],[13,9,2],[9,10]];
  tightCases.push({ name: 'oriented_tight_14_indeg2', adj: tight14, oriented: true });
}
{
  // Bidirected K_{2,3}: M=0, min-deg vertices tie at L*=0, children have L*=2.
  const k23 = [[2,3,4],[2,3,4],[0,1],[0,1],[0,1]];
  assert.equal(exactLstar(k23, 2).gap, 0);
  assert.equal(exactLstar(k23, 0).gap, 2);
  tightCases.push({ name: 'digraph_bidirected_K23', adj: k23, oriented: false });
}
{
  // Bidirected K_{3,3}: 3-out-regular with 2-cycles everywhere, L*=1.
  const k33 = [[3,4,5],[3,4,5],[3,4,5],[0,1,2],[0,1,2],[0,1,2]];
  tightCases.push({ name: 'digraph_bidirected_K33', adj: k33, oriented: false });
}
{
  // 7-vertex 3-out-regular twin-class boundary: B={3,4,5,6} all tie at L*=0, A={0,1,2} have L*=3.
  const k34 = [[3,4,5],[3,5,6],[4,5,6],[0,1,2],[0,1,2],[0,1,2],[0,1,2]];
  assert.equal(exactLstar(k34, 3).gap, 0);
  assert.equal(exactLstar(k34, 0).gap, 3);
  tightCases.push({ name: 'digraph_3reg_twin_boundary', adj: k34, oriented: false });
}
{
  // M=1 sink-free with virtual sink (2-cycle 1 <-> 2): v=0 has d+=1 and L*(0)=0, a=1 has L*(1)>=1.
  const vs = [[1],[2,3,4],[1]];
  addTournamentHub(vs, [0,0,0]);
  assert.equal(exactLstar(vs, 0).gap, 0);
  tightCases.push({ name: 'digraph_M1_virtual_sink', adj: vs, oriented: false });
}

const branchCounts = new Map();
const countBranch = b => branchCounts.set(b, (branchCounts.get(b) ?? 0) + 1);
let qkChecked = 0;

for (const tc of tightCases) {
  const rows = tc.oriented ? inspect(tc.adj) : inspectGeneral(tc.adj);
  const { v, branch } = selectWitness(tc.adj, { orientedOnly: tc.oriented });
  const ls = exactLstar(tc.adj, v);
  assert.ok(ls.gap >= 1, `${tc.name}: L*(${v})=${ls.gap}`);
  assert.ok(rows[v].gap >= ls.gap, `${tc.name}: g < L*`);
  if (tc.oriented && tc.adj.length <= 30) assert.ok(checkRealizations(tc.adj)[v] >= ls.gap);
  const Q = buildSmallQuasiKernel(tc.adj);
  verifySmallQuasiKernel(tc.adj, Q);
  countBranch(branch);
  ++qkChecked;
  console.log(`Tight case ${tc.name}: branch=${branch}, v=${v}, L*(v)=${ls.gap}, g(v)=${rows[v].gap}, |Q|=${Q.length}/${tc.adj.length}`);
}

const fullMode = process.argv.includes('--full') || process.argv.includes('--six');

// 2. Exhaustive oriented graphs (core order 3..5, and 6 with --full) enforcing oriented 1-step rule.
let orientedTotal = 0;
for (const n of (fullMode ? [3, 4, 5, 6] : [3, 4, 5])) {
  const take = n === 6 ? orbitFilter(n) : () => true;
  let count = 0;
  allCores(n, core => {
    if (!take(core)) return;
    attachments(core, (rows, totalN) => {
      const adj = Array.from({ length: totalN }, (_, i) => indices(rows[i] ?? 0));
      const { v, branch } = selectWitness(adj, { orientedOnly: true });
      const ls = exactLstar(adj, v);
      assert.ok(ls.gap >= 1);
      countBranch(branch);
      if (n <= 4 || count % 50 === 0) {
        assert.ok(inspect(adj)[v].gap >= ls.gap);
        const Q = buildSmallQuasiKernel(adj);
        verifySmallQuasiKernel(adj, Q);
        ++qkChecked;
      }
      ++count;
      ++orientedTotal;
    });
  });
  console.log(`Exhaustive oriented core order ${n}: ${count} graphs verified`);
}

// 3. Exhaustive general digraphs WITH 2-cycles (core order 2..4 with <= 2 sinks; core order 5 with <= 1 sink in --full).
let generalExhTotal = 0;
for (const n of (fullMode ? [2, 3, 4, 5] : [2, 3, 4])) {
  const full = (1 << n) - 1;
  const perms = [];
  const gp = (cur, rem) => {
    if (!rem.length) { perms.push(cur); return; }
    for (let i = 0; i < rem.length; ++i) gp([...cur, rem[i]], rem.filter((_, j) => j !== i));
  };
  gp([], Array.from({ length: n }, (_, i) => i));
  const bitPos = Array.from({ length: n }, () => Array(n).fill(-1));
  let bp = 0;
  for (let i = 0; i < n; ++i) for (let j = 0; j < n; ++j) if (i !== j) bitPos[i][j] = bp++;
  const seen = new Uint8Array(1 << bp);
  const opts = Array.from({ length: n }, (_, u) => {
    const o = [];
    for (let m = 1; m <= full; ++m) if (!(m & (1 << u)) && size(m) <= 3) o.push(m);
    return o;
  });
  const core = new Int32Array(n);
  let orbits = 0, count = 0;
  const allowTwoSinks = n <= 4;

  const attach = (idx, sinks, rows) => {
    if (idx === n) {
      const adj = Array.from({ length: n + sinks }, (_, i) => indices(i < n ? rows[i] : 0));
      const { v, branch } = selectWitness(adj);
      const ls = exactLstar(adj, v);
      assert.ok(ls.gap >= 1);
      countBranch(branch);
      if (n <= 4 || count % 50 === 0) {
        assert.ok(inspectGeneral(adj)[v].gap >= ls.gap);
        const Q = buildSmallQuasiKernel(adj);
        verifySmallQuasiKernel(adj, Q);
        ++qkChecked;
      }
      ++count;
      ++generalExhTotal;
      return;
    }
    const base = core[idx], spare = 3 - size(base);
    attach(idx + 1, sinks, rows);
    if (spare >= 1) {
      for (let j = 0; j <= sinks; ++j) {
        rows[idx] = base | (1 << (n + j));
        attach(idx + 1, Math.max(sinks, j + 1), rows);
      }
    }
    if (allowTwoSinks && spare >= 2) {
      for (let j = 0; j <= sinks; ++j) {
        const s1 = Math.max(sinks, j + 1);
        for (let k = j + 1; k <= s1; ++k) {
          rows[idx] = base | (1 << (n + j)) | (1 << (n + k));
          attach(idx + 1, Math.max(s1, k + 1), rows);
        }
      }
    }
    rows[idx] = base;
  };

  const ec = u => {
    if (u === n) {
      let all = 0;
      for (let i = 0; i < n; ++i) all |= core[i];
      if (all !== full) return;
      let id = 0;
      for (let i = 0; i < n; ++i) for (let m = core[i]; m; m &= m - 1) id |= 1 << bitPos[i][31 - Math.clz32(m & -m)];
      if (seen[id]) return;
      const edges = [];
      for (let i = 0; i < n; ++i) for (let m = core[i]; m; m &= m - 1) edges.push([i, 31 - Math.clz32(m & -m)]);
      for (const p of perms) {
        let code = 0;
        for (const [a, b] of edges) code |= 1 << bitPos[p[a]][p[b]];
        seen[code] = 1;
      }
      ++orbits;
      attach(0, 0, core.slice());
      return;
    }
    for (const m of opts[u]) { core[u] = m; ec(u + 1); }
  };
  ec(0);
  console.log(`Exhaustive general 2-cycle core order ${n} (${orbits} orbits): ${count} graphs verified`);
}

// 4. Randomized large-graph tests (up to ~60 vertices; mix of oriented and 2-cycle, 2-sinks, disconnected).
let rng = 20261126;
const rand = () => { rng = (rng * 1664525 + 1013904223) >>> 0; return rng / 4294967296; };
const randInt = k => Math.floor(rand() * k);

let randomTotal = 0;
for (let trial = 0; trial < 5000; ++trial) {
  const coreN = 6 + randInt(35); // 6..40 core vertices
  const style = trial % 8;
  const oriented = style < 2;
  const adj = Array.from({ length: coreN }, () => []);
  const split = style === 7 && coreN >= 8 ? Math.floor(coreN / 2) : coreN;

  if (style === 2) {
    const pairs = coreN % 2 === 1 ? coreN - 3 : coreN;
    for (let i = 0; i < pairs; ++i) adj[i].push(i ^ 1);
    for (let i = pairs; i < coreN; ++i) adj[i].push(pairs + ((i - pairs + 1) % (coreN - pairs)));
  } else if (style === 3) {
    for (let i = 0; i < coreN; ++i) {
      adj[i].push((i + 1) % coreN);
      const prev = (i + coreN - 1) % coreN;
      if (!adj[i].includes(prev)) adj[i].push(prev);
    }
  } else {
    for (let i = 0; i < split; ++i) adj[i].push((i + 1) % split);
    for (let i = split; i < coreN; ++i) adj[i].push(split + ((i - split + 1) % (coreN - split)));
  }

  const maxCoreDeg = style === 4 ? 2 : 3;
  for (let t = 0; t < coreN * 4; ++t) {
    const u = randInt(coreN), w = randInt(coreN);
    if (u === w || adj[u].length >= maxCoreDeg || adj[u].includes(w)) continue;
    if (oriented && adj[w].includes(u)) continue;
    if (style === 7 && (u < split) !== (w < split)) continue;
    adj[u].push(w);
    if (!oriented && rand() < 0.45 && adj[w].length < maxCoreDeg && !adj[w].includes(u)) adj[w].push(u);
  }
  if (style === 1 || style >= 5) {
    let sinks = 0;
    for (let u = 0; u < coreN; ++u) {
      while (adj[u].length < 3 && rand() < (style === 6 ? 0.55 : 0.35)) {
        if (sinks > 0 && rand() < (style === 5 ? 0.7 : 0.3)) {
          const s = coreN + randInt(sinks);
          if (!adj[u].includes(s)) adj[u].push(s); else break;
        } else {
          adj[u].push(coreN + sinks++);
          adj.push([]);
        }
        if (style !== 6) break;
      }
    }
  }
  const rows = oriented ? inspect(adj) : inspectGeneral(adj);
  const { v, branch } = selectWitness(adj, { orientedOnly: oriented });
  const ls = exactLstar(adj, v);
  assert.ok(ls.gap >= 1);
  assert.ok(rows[v].gap >= ls.gap);
  const Q = buildSmallQuasiKernel(adj);
  verifySmallQuasiKernel(adj, Q);
  countBranch(branch);
  ++randomTotal;
  ++qkChecked;
}

console.log({
  orientedTotal,
  generalExhTotal,
  randomTotal,
  qkChecked,
  branches: Object.fromEntries([...branchCounts.entries()].sort())
});
