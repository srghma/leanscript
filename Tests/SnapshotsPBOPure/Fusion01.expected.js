const test = (arr) => {
  // 1. Inlined `fromArray` (Array.foldr) with TCO loop
  let n = arr.length - 1;
  let acc = { tag: "Nil" }; // List.nil

  while (n >= 0) {
    const x = arr[n];

    // Inlined: mapF (· + 1) >>> mapF toString
    const s = (x + 1).toString();

    // Inlined: filterMapF dropPrefix1
    if (s.startsWith("1")) {
      const b = s.slice(1); // (s.drop 1).toString

      // Inlined: mapF ("2" ++ ·)
      const c = "2" + b;

      // Inlined: filterF (· != "wat")
      if (c !== "wat") {
        // Inlined: mapF (· ++ "1") and List.cons
        acc = { tag: "cons", head: c + "1", tail: acc };
      }
    }
    // If filtered out, `acc` is unchanged (zero allocations!)
    n--;
  }

  // 2. Inlined `toArray`: converts the fused List back into a JS Array
  const result = [];
  let curr = acc;
  while (curr.tag === "Cons") {
    result.push(curr.head);
    curr = curr.tail;
  }
  return result;
};

export { test };
