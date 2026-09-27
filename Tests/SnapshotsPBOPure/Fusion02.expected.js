const test = (arr) => {
  let ix = 0;
  let acc = { tag: "Nil" }; // List.nil

  while (ix < arr.length) {
    const x = arr[ix];
    ix++; // State advanced

    const s = (x + 1).toString();
    if (s.startsWith("1")) {
      const b = s.slice(1);
      const c = "2" + b;
      if (c !== "wat") {
        acc = { tag: "Cons", head: c + "1", tail: acc };
      }
    }
  }

  // toArray reverses the accumulator since it was prepended
  const res = [];
  let curr = acc;
  while (curr.tag === "Cons") {
    res.push(curr.head);
    curr = curr.tail;
  }
  return res.reverse();
};

export { test };
