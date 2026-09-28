// const test1 = f => a => b => {
//   if (f(a) && f(b) ? f(a) : true) { return f(a); }
//   return f();
// };
// export {test1};

const test1 = (f) => (a) => {
  const $0 = f(a);
  return (b) => {
    if ($0 && f(b) ? $0 : true) {
      return $0;
    }
    return f();
  }
};
export { test1 };
