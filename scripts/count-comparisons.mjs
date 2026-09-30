// Run a two-argument function of a generated module on a grid of integer arguments, counting
// the comparisons with an integer literal (`v === 4`, `v !== 4n`) each call evaluates.
//
//   node count-comparisons.mjs FILE.js FUNCTION CURRIED XS YS
//   node count-comparisons.mjs FILE.js FUNCTION CURRIED XS
//
// CURRIED is `1` for `f(x)(y)` (purescript-backend-optimizer) and `0` for `f(x, y)`; XS and YS
// are JSON arrays of integers (passed as BigInts when the module compares with BigInt
// literals).  Prints one line `x,y,result,comparisons` per pair; without YS the function takes
// one argument, and each line is `x,result,comparisons`.
import { readFileSync } from "node:fs";

const [file, fn, curried, xsJson, ysJson] = process.argv.slice(2);
let comparisons = 0;
globalThis.__cmp = (a, op, b) => {
  comparisons++;
  return op === "===" ? a === b : a !== b;
};
const src = readFileSync(file, "utf8").replace(
  /\b(\w+) (===|!==) (-?\d+n?)\b/g,
  (_, a, op, b) => `__cmp(${a}, "${op}", ${b})`,
);
const M = await import("data:text/javascript," + encodeURIComponent(src));
const big = /\b\d+n\b/.test(src);
const lift = (v) => (big ? BigInt(v) : v);
const out = [];
for (const x of JSON.parse(xsJson)) {
  if (ysJson === undefined) {
    comparisons = 0;
    const r = M[fn](lift(x));
    out.push(`${x},${r},${comparisons}`);
    continue;
  }
  for (const y of JSON.parse(ysJson)) {
    comparisons = 0;
    const r = curried === "1" ? M[fn](lift(x))(lift(y)) : M[fn](lift(x), lift(y));
    out.push(`${x},${y},${r},${comparisons}`);
  }
}
console.log(out.join("\n"));
