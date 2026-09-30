// Run a two-argument function of a generated module on a grid of numeric arguments, counting
// the comparisons with a numeric literal (`v === 4`, `v !== 4n`, `v === 1.0`) each call
// evaluates.
//
//   node count-comparisons.mjs FILE.js FUNCTION CURRIED XS YS
//   node count-comparisons.mjs FILE.js FUNCTION CURRIED XS
//   node count-comparisons.mjs FILE.js FUNCTION record TUPLES
//   node count-comparisons.mjs FILE.js FUNCTION spread TUPLES
//
// CURRIED is `1` for `f(x)(y)` (purescript-backend-optimizer) and `0` for `f(x, y)`; XS and YS
// are JSON arrays of numbers (integers are passed as BigInts when the module compares with BigInt
// literals).  Prints one line `x,y,result,comparisons` per pair; without YS the function takes
// one argument, and each line is `x,result,comparisons`.  A call that throws has the result
// `threw: MESSAGE` (a `panic!`).  With `record` (resp. `spread`), TUPLES is a JSON array of arrays
// of numbers, and the function is called on the record `{ _1: x1, _2: x2, … }` of each (resp. as
// `f(x1, x2, …)`, as purescript-backend-optimizer spells a product's fields); each line is
// `x1;x2;…,result,comparisons`.  A tuple may nest (`[[1, 2], [3, 4]]`): with `record` the
// function gets nested records (`{ _1: { _1: 1, _2: 2 }, _2: { … } }`), with `spread` the
// flattened fields (`f(1, 2, 3, 4)`), and the line lists the flattened fields.  The compared
// operand may be a name with `$` or a field read (`f$1 === 4`, `x._3 === 1`); orderings with a
// numeric literal (`0 < f$1`, `v_a > 0`) are counted too.
import { readFileSync } from "node:fs";

const [file, fn, curried, xsJson, ysJson] = process.argv.slice(2);
let comparisons = 0;
const ops = {
  "===": (a, b) => a === b,
  "!==": (a, b) => a !== b,
  "<": (a, b) => a < b,
  ">": (a, b) => a > b,
  "<=": (a, b) => a <= b,
  ">=": (a, b) => a >= b,
};
globalThis.__cmp = (a, op, b) => {
  comparisons++;
  return ops[op](a, b);
};
const src = readFileSync(file, "utf8")
  .replace(
    /(?<![\w$.])([\w$]+(?:\.[\w$]+)*) (===|!==|<=|>=|<|>) (-?\d+(?:\.\d+)?n?)(?![\w$.])/g,
    (_, a, op, b) => `__cmp(${a}, "${op}", ${b})`,
  )
  .replace(
    /(?<![\w$.])(-?\d+(?:\.\d+)?n?) (<=|>=|<|>) ([\w$]+(?:\.[\w$]+)*)(?![\w$.(])/g,
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
if (curried === "record" || curried === "spread") {
  for (const t of JSON.parse(xsJson)) {
    comparisons = 0;
    const toRecord = (v) =>
      Array.isArray(v) ? Object.fromEntries(v.map((w, i) => ["_" + (i + 1), toRecord(w)])) : lift(v);
    const flat = t.flat(Infinity);
    const r = call(() =>
      curried === "record" ? M[fn](toRecord(t)) : M[fn](...flat.map(lift)),
    );
    out.push(`${flat.join(";")},${r},${comparisons}`);
  }
  console.log(out.join("\n"));
  process.exit(0);
}
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
