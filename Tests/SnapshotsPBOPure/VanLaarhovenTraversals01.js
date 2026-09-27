import {
  Repr_addAppParen,
  String_quote,
} from "../runtime/lean_runtime_non_configurable.mjs";
const traverseFun1D__at__rewriteBottomUpM__at__rewriteBottomUp_spec_0_spec_0 = (
  v0,
  v1,
) => {
  if (v0.tag === 0) {
    return { tag: 0, _1: v0._1, _2: v1(v0._2) };
  } else {
    return { tag: 1, _1: v1(v0._1), _2: v1(v0._2) };
  }
};
const rewriteBottomUpM__at__rewriteBottomUp_spec_0 = (
  v0,
  v1,
) => v0(
  traverseFun1D__at__rewriteBottomUpM__at__rewriteBottomUp_spec_0_spec_0(
    v1,
    (v2) => rewriteBottomUpM__at__rewriteBottomUp_spec_0(v0, v2),
  ),
);
export const instReprFun_repr = (v0, v1) => {
  if (v0.tag === 0) {
    const v2 = v0._1;
    const v3 = v0._2;
    const v4 = (v4) => {
      const v5 = { tag: 1 };
      return Repr_addAppParen(
        {
          tag: 6,
          _1: {
            tag: 4,
            _1: v4,
            _2: {
              tag: 5,
              _1: {
                tag: 5,
                _1: {
                  tag: 5,
                  _1: { tag: 5, _1: { tag: 3, _1: "Fun.Abs" }, _2: v5 },
                  _2: { tag: 3, _1: String_quote(v2) },
                },
                _2: v5,
              },
              _2: instReprFun_repr(v3, 1024),
            },
          },
          _2: { tag: 0 },
        },
        v1,
      );
    };
    if (1024 <= v1) {
      return v4(1);
    } else {
      return v4(2);
    }
  } else {
    const v2 = v0._1;
    const v3 = v0._2;
    const v4 = (v4) => {
      const v5 = { tag: 1 };
      return Repr_addAppParen(
        {
          tag: 6,
          _1: {
            tag: 4,
            _1: v4,
            _2: {
              tag: 5,
              _1: {
                tag: 5,
                _1: {
                  tag: 5,
                  _1: { tag: 5, _1: { tag: 3, _1: "Fun.App" }, _2: v5 },
                  _2: instReprFun_repr(v2, 1024),
                },
                _2: v5,
              },
              _2: instReprFun_repr(v3, 1024),
            },
          },
          _2: { tag: 0 },
        },
        v1,
      );
    };
    if (1024 <= v1) {
      return v4(1);
    } else {
      return v4(2);
    }
  }
};
export const instDecidableEqFun_decEq = (v0, v1) => {
  if (v0.tag === 0) {
    if (v1.tag === 0) {
      if (v0._1 === v1._1) {
        if (instDecidableEqFun_decEq(v0._2, v1._2)) {
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else {
    if (v1.tag === 0) {
      return false;
    } else {
      if (instDecidableEqFun_decEq(v0._1, v1._1)) {
        if (instDecidableEqFun_decEq(v0._2, v1._2)) {
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    }
  }
};
export const Fun_size = (v0) => {
  if (v0.tag === 0) {
    return Fun_size(v0._2) + 1;
  } else {
    return Fun_size(v0._1) + Fun_size(v0._2) + 1;
  }
};
export const traverseFun1D = (v0, v1, v2, v3, v4, v5, v6) => {
  if (v5.tag === 0) {
    const v7 = v5._1;
    return v0._1((v8) => ({ tag: 0, _1: v7, _2: v8 }), v6(v5._2));
  } else {
    const v7 = v5._2;
    return v2(
      v0._1((v8, v9) => ({ tag: 1, _1: v8, _2: v9 }), v6(v5._1)),
      (v8) => {
        const v9 = v6(v7);
        return () => v9;
      },
    );
  }
};
export const traverseFun1 = (v0, v1, v2, v3, v4, v5, v6) => {
  if (v6.tag === 0) {
    const v7 = v6._1;
    return v0._1((v8) => ({ tag: 0, _1: v7, _2: v8 }), v5(v6._2));
  } else {
    const v7 = v6._2;
    return v2(
      v0._1((v8, v9) => ({ tag: 1, _1: v8, _2: v9 }), v5(v6._1)),
      (v8) => {
        const v9 = v5(v7);
        return () => v9;
      },
    );
  }
};
export const rewriteBottomUpM = (
  v0,
  v1,
  v2,
  v3,
) => v1(
  traverseFun1D(
    v0._1,
    v0._2,
    v0._3,
    v0._4,
    v0._5,
    v3,
    (v4) => rewriteBottomUpM(v0, v1, v2, v4),
  ),
  (v4) => v2(v4),
);
export const rewriteBottomUp = (
  v0,
  v1,
) => rewriteBottomUpM__at__rewriteBottomUp_spec_0((v2) => v0(v2), v1);
export const instReprFun_reprPrec = instReprFun_repr;
export const instDecidableEqFun = instDecidableEqFun_decEq;
