import {
  Int_instDecidableEq,
} from "../runtime/lean_runtime_non_configurable.mjs";
const _spec$test1 = (v0) => {
  let v1 = v0;
  while (true) {
    if (Int_instDecidableEq(v1, 1)) {
      return v1;
    } else {
      const v2 = v1 - 1;
      if (Int_instDecidableEq(v2, 2)) {
        return v2;
      } else {
        v1 = v2 - 2;
        continue;
      }
    }
  }
};
export const test1 = _spec$test1;
export const test2 = (v0) => {
  if (Int_instDecidableEq(v0, 2)) {
    return v0;
  } else {
    return _spec$test1(v0 - 2);
  }
};
