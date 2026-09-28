const $Color$Red = "Red";
const $Color$Black = "Black";
const $RedBlackTree$Leaf = {
  tag: "Leaf",
};
const $RedBlackTree$Node = (color, l, val, r) => ({
  tag: "Node",
  _color: color,
  _l: l,
  _val: val,
  _r: r,
});
const test1 = (v) => {
  if (v.tag === "Node" && v._color === "Black") {
    if (v._l.tag === "Node" && v._l._color === "Red") {
      if (v._l._l.tag === "Node" && v._l._l._color === "Red") {
        return {
          i: 1,
          a: v._l._l._l,
          x: v._l._l._val,
          b: v._l._l._r,
          y: v._l._val,
          c: v._l._r,
          z: v._val,
          d: v._r,
        };
      }
      if (v._l._r.tag === "Node" && v._l._r._color === "Red") {
        return {
          i: 2,
          a: v._l._l,
          x: v._l._val,
          b: v._l._r._l,
          y: v._l._r._val,
          c: v._l._r._r,
          z: v._val,
          d: v._r,
        };
      }
    }
    if (v._r.tag === "Node" && v._r._color === "Red") {
      if (v._r._l.tag === "Node" && v._r._l._color === "Red") {
        return {
          i: 3,
          a: v._l,
          x: v._val,
          b: v._r._l._l,
          y: v._r._l._val,
          c: v._r._l._r,
          z: v._r._val,
          d: v._r._r,
        };
      }
      if (v._r._r.tag === "Node" && v._r._r._color === "Red") {
        return {
          i: 4,
          a: v._l,
          x: v._val,
          b: v._r._l,
          y: v._r._val,
          c: v._r._r._l,
          z: v._r._r._val,
          d: v._r._r._r,
        };
      }
    }
  }
  throw new Error("UNREACHABLE");
};
export {
  $Color$Black,
  $Color$Red,
  $RedBlackTree$Leaf,
  $RedBlackTree$Node,
  test1,
};
