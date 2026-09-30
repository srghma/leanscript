// Run `test1` of the generated `CaseSum` module and of purescript-backend-optimizer's
// `legacy-backend/CaseSum.js` on a list of values, counting the comparisons with a literal and
// the reads of the value each call makes.
//
//   node sum-compare.mjs OURS.js PBO.js VALUES
//
// VALUES is a JSON array of values `["L" | "R", n]` (`SumType.L n` / `SumType.R n`).  Our module
// represents `L n` as `{ tag: 0, _1: n }` and `R n` as `{ tag: 1, _1: n }` (`n` a BigInt when the
// module compares with BigInt literals); PBO's as `{ tag: "L", _n: n }` and `{ tag: "R", _n: n }`.
// A comparison is an `===` / `!==` with a numeric or string literal (`v.tag === 0`,
// `f$1 === 2n`, `v.tag === "L"`); a read is a read of the property `tag` or of the field
// (`_1` resp. `_n`) of the value.  Prints one line per value:
// `ours|pbo|oursComparisons|pboComparisons|oursReads|pboReads`, each result the string answered
// or `threw: MESSAGE`.
import { readFileSync } from "node:fs";

const [oursFile, pboFile, valuesJson] = process.argv.slice(2);
let comparisons = 0;
let reads = 0;
globalThis.__cmp = (a, op, b) => {
  comparisons++;
  return op === "===" ? a === b : a !== b;
};
const load = async (file) => {
  const src = readFileSync(file, "utf8").replace(
    /(?<![\w$.])([\w$]+(?:\.[\w$]+)*) (===|!==) (-?\d+n?(?![\w$.])|"(?:[^"\\\n]|\\.)*")/g,
    (_, a, op, b) => `__cmp(${a}, "${op}", ${b})`,
  );
  return [await import("data:text/javascript," + encodeURIComponent(src)), /\b\d+n\b/.test(src)];
};
const [ours, big] = await load(oursFile);
const [pbo] = await load(pboFile);

const counting = (obj) =>
  new Proxy(obj, {
    get(t, k) {
      if (typeof k === "string") reads++;
      return t[k];
    },
  });

const run = (thunk) => {
  comparisons = 0;
  reads = 0;
  let r;
  try {
    r = String(thunk());
  } catch (e) {
    r = `threw: ${e.message}`;
  }
  return [r, comparisons, reads];
};

const out = [];
for (const [c, n] of JSON.parse(valuesJson)) {
  const [o, oc, or] = run(() =>
    ours.test1(counting({ tag: c === "L" ? 0 : 1, _1: big ? BigInt(n) : n })));
  const [p, pc, pr] = run(() => pbo.test1(counting({ tag: c, _n: n })));
  out.push(`${o}|${p}|${oc}|${pc}|${or}|${pr}`);
}
console.log(out.join("\n"));
