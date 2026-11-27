import assert from 'node:assert/strict';
import { inspect } from '../shared/clow-check.mjs';

// Bit i switches the two copies of the i-th arc in row order.
function doubleCover(out, switches) {
  let i = 0;
  const lift = Array.from({ length: 2 * out.length }, () => []);
  for (const [u, next] of out.entries()) {
    for (const v of next) {
      const flip = (switches >> i++) & 1;
      for (const side of [0,1]) lift[2*u+side].push(2*v+(side^flip));
    }
  }
  return lift;
}

const fork = [[1,2],[3,4],[3,5],[0,6],[],[],[]];
const base = inspect(fork);
assert.equal(base[0].gap, 1);
const edgeCount = fork.reduce((sum, row) => sum + row.length, 0);
let ties = 0, minGood = 2 * fork.length;
for (let switches = 0; switches < 2 ** edgeCount; ++switches) {
  const rows = inspect(doubleCover(fork, switches));
  if (rows[0].gap === 0) ++ties;
  assert.equal(rows[0].gap, rows[1].gap);
  minGood = Math.min(minGood, rows.filter(r => r.gap > 0).length);
  for (const row of rows) {
    const root = base[Math.floor(row.v / 2)];
    const projected = row.S.map(v => Math.floor(v / 2));
    assert.equal(new Set(projected).size, projected.length);
    assert.ok(projected.every(s => root.S.includes(s)));
    for (const s of root.S.filter(s => fork.filter(neighbors => neighbors.includes(s)).length === 1)) {
      assert.ok(projected.includes(s));
    }
  }
}
// Only the arc 2 -> 3 is crossed.
assert.deepEqual(inspect(doubleCover(fork, 1 << 4))[0].S, [8,10]);
console.log({ switches: 2 ** edgeCount, tiesAtRoot: ties, minimumGoodVertices: minGood });

// Select a witness under the lemma's hypothesis. Gap queries are needed only
// for the chosen vertex next to a sink, before deciding whether to move once.
function choose(out, gapAt) {
  assert.ok(out.every((row, v) => !row.length || out.filter(a => a.includes(v)).length >= 2));
  const sinks = out.map(row => row.length === 0);
  const sinkChildren = out.map(row => row.filter(w => sinks[w]));
  const onlySinks = out.findIndex((row, v) => row.length && row.length === sinkChildren[v].length);
  if (onlySinks >= 0) return onlySinks;
  const two = sinkChildren.findIndex(row => row.length >= 2);
  if (two >= 0) return gapAt(two) > 0 ? two : out[two].find(w => !sinks[w]);
  const v = sinkChildren.findIndex(row => row.length > 0);
  if (v >= 0) return gapAt(v) > 0 ? v : out[v].find(w => !sinks[w]);
  return out.reduce((best, row, i) => row.length < out[best].length ? i : best, 0);
}

function checkChoice(out) {
  const rows = inspect(out);
  const selected = choose(out, v => rows[v].gap);
  assert.ok(rows[selected].gap > 0);
  return selected;
}

// A five-vertex regular tournament provides spare incoming arcs to the gadget.
const tight = [
  [1,2,6],[3,4,7],[3,4,8],[5],[5],[9],[],[],[],
  [10,11,0],[11,12,0],[12,13,1],[13,9,2],[9,10]
];
const tightRows = inspect(tight);
assert.equal(tightRows[0].gap, 0);
assert.ok(tightRows[1].gap > 0 && tightRows[2].gap > 0);
assert.equal(checkChoice(tight), 1);

// Vary all attachments of zero or one private/shared sink per tournament vertex.
let attachments = 0;
for (let code = 0; code < 3**5; ++code) {
  const out = Array.from({length:5}, (_,i) => [(i+1)%5,(i+2)%5]);
  let value = code;
  const used = new Map();
  for (let i = 0; i < 5; ++i) {
    const choice = value % 3;
    value = Math.floor(value / 3);
    if (!choice) continue;
    if (!used.has(choice)) { used.set(choice, out.length); out.push([]); }
    out[i].push(used.get(choice));
  }
  checkChoice(out);
  ++attachments;
}
console.log({ tournamentAttachments: attachments, tightWitness: 1 });
