const _mut$go = (v0, v1) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v2 === 0) {
      if (v3 === 0) {
        return v3;
      } else {
        if (v3 <= 100) {
          v2 = 0;
          v3 = v3 - 1;
          continue;
        } else {
          v2 = 1;
          v3 = v3 - 1;
          continue;
        }
      }
    } else {
      if (v3 === 100) {
        v2 = 0;
        v3 = Math.max(0, v3 - 1);
        continue;
      } else {
        if (v3 === 900) {
          return 42;
        } else {
          v2 = 1;
          v3 = Math.max(0, v3 - 1);
          continue;
        }
      }
    }
  }
};
export const go = (v0) => _mut$go(0, v0);
export const k = (v0) => _mut$go(1, v0);
