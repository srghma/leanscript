// Run `test1` of the generated `CaseRedBlackTree` module and of purescript-backend-optimizer's
// `legacy-backend/CaseRedBlackTree.js` on a list of trees, counting the tests each call makes.
//
//   node rbt-compare.mjs OURS.js PBO.js TREES
//
// TREES is a JSON array of trees: `null` is `Leaf`, `["R" | "B", l, v, r]` is `Node c l v r`.
// Our module represents `Leaf` as `{ tag: 0 }` and `Node c l v r` as
// `{ tag: 1, _1: c === Black, _2: l, _3: v, _4: r }` (`v` a BigInt when the module compares
// with BigInt literals); PBO's as `{ tag: "Leaf" }` and
// `{ tag: "Node", _color: "Red" | "Black", _l, _val, _r }`.
// A test is a read of the constructor (`tag`) or of the colour (`_1` resp. `_color`) of a
// tree.  Prints one line per tree: `ours|pbo|oursTests|pboTests`, each result written as
// `i;a;x;b;y;c;z;d` with the trees as `L` / `N(R,l,v,r)`, or `threw: MESSAGE`.
import { readFileSync } from "node:fs";

const [oursFile, pboFile, treesJson] = process.argv.slice(2);
const load = async (file) =>
  import("data:text/javascript," + encodeURIComponent(readFileSync(file, "utf8")));
const ours = await load(oursFile);
const pbo = await load(pboFile);
const big = /\b\d+n\b/.test(readFileSync(oursFile, "utf8"));

let tests = 0;
const counting = (obj, keys) =>
  new Proxy(obj, {
    get(t, k) {
      if (keys.includes(k)) tests++;
      return t[k];
    },
  });

const toOurs = (t) =>
  t === null
    ? counting({ tag: 0 }, ["tag", "_1"])
    : counting(
        { tag: 1, _1: t[0] === "B", _2: toOurs(t[1]), _3: big ? BigInt(t[2]) : t[2], _4: toOurs(t[3]) },
        ["tag", "_1"],
      );
const toPbo = (t) =>
  t === null
    ? counting({ tag: "Leaf" }, ["tag", "_color"])
    : counting(
        { tag: "Node", _color: t[0] === "B" ? "Black" : "Red", _l: toPbo(t[1]), _val: t[2], _r: toPbo(t[3]) },
        ["tag", "_color"],
      );

// reading the answers back does not count: `tests` is taken before
const showOurs = (t) => {
  const tag = Reflect.get(t, "tag");
  if (tag === 0) return "L";
  return `N(${t._1 ? "B" : "R"},${showOurs(t._2)},${t._3},${showOurs(t._4)})`;
};
const showPbo = (t) => {
  if (t.tag === "Leaf") return "L";
  return `N(${t._color === "Black" ? "B" : "R"},${showPbo(t._l)},${t._val},${showPbo(t._r)})`;
};

const run = (thunk, show) => {
  tests = 0;
  try {
    const r = thunk();
    const n = tests;
    return [show(r), n];
  } catch (e) {
    return [`threw: ${e.message}`, tests];
  }
};

const out = [];
for (const t of JSON.parse(treesJson)) {
  const [o, on] = run(() => ours.test1(toOurs(t)), (r) =>
    [r._1, showOurs(r._2), r._3, showOurs(r._4), r._5, showOurs(r._6), r._7, showOurs(r._8)].join(";"));
  const [p, pn] = run(() => pbo.test1(toPbo(t)), (r) =>
    [r.i, showPbo(r.a), r.x, showPbo(r.b), r.y, showPbo(r.c), r.z, showPbo(r.d)].join(";"));
  out.push(`${o}|${p}|${on}|${pn}`);
}
console.log(out.join("\n"));
