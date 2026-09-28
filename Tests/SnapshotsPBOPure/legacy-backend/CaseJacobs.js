export const renderExpr = (v0) => {
  if (v0.tag === 0) {
    return "Add(" + renderExpr(v0._1) + " " + renderExpr(v0._2) + ")";
  } else {
    if (v0.tag === 1) {
      return "Mul(" + renderExpr(v0._1) + " " + renderExpr(v0._2) + ")";
    } else {
      if (v0.tag === 2) {
        return "Succ(" + renderExpr(v0._1) + ")";
      } else {
        return "Zero";
      }
    }
  }
};
export const test1 = (v0) => {
  if (v0.tag === 0) {
    const v1 = v0._1;
    const v2 = v0._2;
    if (v1.tag === 3) {
      if (v2.tag === 3) {
        return "e1";
      } else {
        return "e7: " + renderExpr(v0);
      }
    } else {
      if (v1.tag === 2) {
        return "e3: " + renderExpr(v1._1) + " " + renderExpr(v2);
      } else {
        if (v2.tag === 3) {
          return "e6: " + renderExpr(v1);
        } else {
          return "e7: " + renderExpr(v0);
        }
      }
    }
  } else {
    if (v0.tag === 1) {
      const v1 = v0._1;
      const v2 = v0._2;
      if (v1.tag === 3) {
        return "e2: " + renderExpr(v2);
      } else {
        if (v1.tag === 0) {
          if (v2.tag === 3) {
            return "e4: " + renderExpr(v1);
          } else {
            return "e5: " + renderExpr(v1._1) + " " + renderExpr(v1._2) + " " +
              renderExpr(v2);
          }
        } else {
          if (v2.tag === 3) {
            return "e4: " + renderExpr(v1);
          } else {
            return "e7: " + renderExpr(v0);
          }
        }
      }
    } else {
      return "e7: " + renderExpr(v0);
    }
  }
};
export const instToStringExpr_toString = renderExpr;
