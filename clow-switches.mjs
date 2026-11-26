import { inspect } from './clow-check.mjs';

// Renaming the two copies at one vertex toggles all incident switches.
// Fix forest switches to zero: each remaining choice is one representative.
export function eachDoubleCover(out, visit) {
  const parent = out.map((_,v) => v);
  function root(v) {
    while (v !== parent[v]) v = parent[v];
    return v;
  }
  let free = 0;
  const edges = out.flatMap((row,u) => row.map(v => {
    const a = root(u), b = root(v);
    if (a === b) return { u, v, switchBit: 2 ** free++ };
    parent[a] = b;
    return { u, v, switchBit: 0 };
  }));
  if (free > 20) throw new RangeError('More than 20 independent switches');
  for (let mask=0; mask<2**free; ++mask) {
    const lift = Array.from({length:2*out.length}, () => []);
    for (const {u,v,switchBit} of edges) {
      const flip = Number(Boolean(mask & switchBit));
      lift[2*u].push(2*v+flip);
      lift[2*u+1].push(2*v+1-flip);
    }
    visit(inspect(lift), mask, lift);
  }
}
