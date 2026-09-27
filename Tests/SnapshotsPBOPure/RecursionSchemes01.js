import { Function_const } from "../runtime/lean_runtime_non_configurable.mjs";
export const mapExprF = (v0, v1) => {
  if (v1.tag === 0) {
    return { tag: 0, _1: v1._1 };
  } else {
    if (v1.tag === 1) {
      return { tag: 1, _1: v0(v1._1), _2: v0(v1._2) };
    } else {
      return { tag: 2, _1: v0(v1._1), _2: v0(v1._2) };
    }
  }
};
export const instFunctorExprF_map = mapExprF;
export const instFunctorExprF_mapConst = (
  v0,
  v1,
) => mapExprF((v2) => Function_const(v0, v2), v1);
export const eval$ = (v0) => {
  if (v0.tag === 0) {
    return v0._1;
  } else {
    if (v0.tag === 1) {
      return v0._1 + v0._2;
    } else {
      return v0._1 * v0._2;
    }
  }
};
export const bump = (v0) => {
  if (v0.tag === 0) {
    return { tag: 0, _1: v0._1 + 1 };
  } else {
    return v0;
  }
};
export const test2 = (v0) => cata((v1) => eval$(bump(v1)), v0);
export const test1 = (v0) => cata(eval$, v0);
export const cataMap = (v0, v1) => {
  if (v1.tag === 0) {
    return { tag: 0, _1: v1._1 };
  } else {
    if (v1.tag === 1) {
      return { tag: 1, _1: cata(v0, v1._1), _2: cata(v0, v1._2) };
    } else {
      return { tag: 2, _1: cata(v0, v1._1), _2: cata(v0, v1._2) };
    }
  }
};
export const cata = (v0, v1) => v0(cataMap(v0, v1));
