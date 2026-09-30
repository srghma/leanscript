// Run a two-argument function of a generated module on a grid of numeric arguments, counting
// the comparisons with a numeric literal (`v === 4`, `v !== 4n`, `v === 1.0`) each call
// evaluates.
//
//   node count-comparisons.mjs FILE.js FUNCTION CURRIED XS YS
//   node count-comparisons.mjs FILE.js FUNCTION CURRIED XS
//
// CURRIED is `1` for `f(x)(y)` (purescript-backend-optimizer) and `0` for `f(x, y)`; XS and YS
// are JSON arrays of numbers (integers are passed as BigInts when the module compares with BigInt
// literals).  Prints one line `x,y,result,comparisons` per pair; without YS the function takes
// one argument, and each line is `x,result,comparisons`.  A call that throws has the result
// `threw: MESSAGE` (a `panic!`).
import { readFileSync } from "node:fs";

const [file, fn, curried, xsJson, ysJson] = process.argv.slice(2);
let comparisons = 0;
globalThis.__cmp = (a, op, b) => {
  comparisons++;
  return op === "===" ? a === b : a !== b;
};
const src = readFileSync(file, "utf8").replace(
  /\b(\w+) (===|!==) (-?\d+(?:\.\d+)?n?)\b/g,
  (_, a, op, b) => `__cmp(${a}, "${op}", ${b})`,
);
const M = await import("data:text/javascript," + encodeURIComponent(src));
const big = /\b\d+n\b/.test(src);
const lift = (v) => (big ? BigInt(v) : v);
const call = (thunk) => {
  try {
    return thunk();
  } catch (e) {
    return `threw: ${e.message}`;
  }
};
const out = [];
for (const x of JSON.parse(xsJson)) {
  if (ysJson === undefined) {
    comparisons = 0;
    const r = call(() => M[fn](lift(x)));
    out.push(`${x},${r},${comparisons}`);
    continue;
  }
  for (const y of JSON.parse(ysJson)) {
    comparisons = 0;
    const r = call(() => (curried === "1" ? M[fn](lift(x))(lift(y)) : M[fn](lift(x), lift(y))));
    out.push(`${x},${y},${r},${comparisons}`);
  }
}
console.log(out.join("\n"));
