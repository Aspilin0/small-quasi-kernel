import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';

// Direct definition: delete vertices, then test for surviving incoming arcs.
export function inspect(out, degreeLimit = 3) {
  const vertices = out.map((_, i) => i);
  assert.ok(vertices.length > 0);
  for (const v of vertices) {
    const next = out[v];
    assert.ok(next.length <= degreeLimit && new Set(next).size === next.length);
    for (const w of next) {
      assert.ok(Number.isInteger(w) && w >= 0 && w < out.length);
      assert.ok(w !== v && !out[w].includes(v));
    }
    assert.ok(out.some(row => row.includes(v)), 'source in input');
  }
  return vertices.map(v => {
    const rest = vertices.filter(w => w !== v && !out[v].includes(w));
    const S = rest.filter(w => !rest.some(u => out[u].includes(w)));
    const E = Array.from(new Set([...out[v], ...S.flatMap(w => out[w])])).sort((a,b) => a-b);
    return { v, S, E, gap: E.length - S.length };
  });
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  console.log(JSON.stringify(inspect(JSON.parse(readFileSync(0, 'utf8'))), null, 2));
}
