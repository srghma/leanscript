/-! The two layouts of `List` (`MoreJs.ListRepr`): tagged cons cells in the faithful preset
(`{ tag: 0 }`, `{ tag: 1, _1: head, _2: tail }`), JavaScript arrays in the pbo preset. -/
namespace ListRepr

/-- A constant list: shared cons cells `{ tag: 1, _1: 1n, _2: … $tag0 }`. -/
def x : List Nat := [1, 2, 3]

/-- The empty list. -/
def empty : List String := []

/-- Elements in front of a list: the list is the tail of the cells, shared. -/
def front (a : String) (xs : List String) : List String := [a, "b"] ++ xs

/-- A list after elements and before others: copied, then shared tail. -/
def middle (xs : List Nat) : List Nat := [0] ++ xs ++ [7, 8]

/-- An append: the cells of the first list are copied, the second is shared. -/
def append (xs ys : List Nat) : List Nat := xs ++ ys

/-- `Array.toList` and `List.toArray`: the conversions of the runtime. -/
def ofArr (a : Array Nat) : List Nat := a.toList
def toArr (xs : List Nat) : Array Nat := xs.toArray

/-- A round trip is the list itself. -/
def roundTrip (xs : List Int) : List Int := xs.toArray.toList

/-- A list of lists. -/
def nested (xs : List Nat) : List (List Nat) := [xs, [1], xs]

end ListRepr
