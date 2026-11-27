export const bit = i => 1 << i;
// Core of the published 24-vertex example, in its original labelling.
export const referenceCore = [[4,5],[3,7],[0,6],[2,4],[2,7],[1,6],[0,1],[3,5]];
export function size(mask) {
  let n = 0;
  while (mask) { mask &= mask - 1; ++n; }
  return n;
}
export function indices(mask) {
  const result = [];
  while (mask) {
    const low = mask & -mask;
    result.push(31 - Math.clz32(low));
    mask ^= low;
  }
  return result;
}

// Label the core. A new sink gets its index on first use, so a choice of
// attached vertices and a partition into shared sinks is visited exactly once.
export function attachments(core, visit) {
  const n = core.length;
  const rows = core.slice();
  function extend(i, sinks) {
    if (i === n) {
      visit(rows, n + sinks);
      return;
    }
    extend(i + 1, sinks);
    if (size(core[i]) >= 3) return;
    for (let j = 0; j <= sinks; ++j) {
      rows[i] = core[i] | bit(n + j);
      extend(i + 1, Math.max(sinks, j + 1));
    }
    rows[i] = core[i];
  }
  extend(0, 0);
}

export function allCores(n, visit, { allowZeroDegree = false } = {}) {
  const rows = Array(n).fill(0);
  const pairs = [];
  for (let i = 0; i < n; ++i)
    for (let j = i + 1; j < n; ++j) pairs.push([i,j]);
  function extend(p) {
    if (p === pairs.length) {
      if (allowZeroDegree || (rows.every(row => row !== 0) && rows.reduce((a,b) => a | b, 0) === bit(n)-1))
        visit(rows);
      return;
    }
    const [i,j] = pairs[p];
    extend(p + 1);
    for (const [u,v] of [[i,j],[j,i]]) {
      if (size(rows[u]) === 3) continue;
      rows[u] |= bit(v);
      extend(p + 1);
      rows[u] ^= bit(v);
    }
  }
  extend(0);
}

// For six vertices, visit one labelled representative of each core orbit.
// Sink attachments are still fully enumerated on that representative.
export function orbitFilter(n) {
  const weights = Array.from({length:n}, () => Array(n).fill(0));
  let power = 1;
  for (let u=0; u<n; ++u) for (let v=u+1; v<n; ++v) {
    weights[u][v] = power; weights[v][u] = 2*power; power *= 3;
  }
  const seen = new Uint8Array(power);
  const permutations = [];
  function permute(prefix, left) {
    if (!left.length) { permutations.push(prefix); return; }
    for (const v of left) permute([...prefix,v], left.filter(w => w !== v));
  }
  permute([], Array.from({length:n}, (_,v) => v));
  return rows => {
    let id = 0;
    for (const [u,mask] of rows.entries()) for (let m=mask; m; m &= m-1)
      id += weights[u][31-Math.clz32(m & -m)];
    if (seen[id]) return false;
    const edges = rows.flatMap((mask,u) => indices(mask).map(v => [u,v]));
    for (const p of permutations) {
      let code = 0;
      for (const [u,v] of edges) code += weights[p[u]][p[v]];
      seen[code] = 1;
    }
    return true;
  };
}
