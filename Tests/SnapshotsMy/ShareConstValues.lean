-- The value of a constant reads the values of the constants before it by their names
-- (`shareConstValues`, `JsTerm/Lower/ShareConsts.lean`).

def table : Array Nat := #[1, 2, 3]

-- the whole value: `export const same = table;`
def same : Array Nat := #[1, 2, 3]

-- a part of the value: `export const nested = [table, [4]];`
def nested : Array (Array Nat) := #[table, #[4]]

-- the whole value of `nested`, through its own definition: `export const nested2 = nested;`
def nested2 : Array (Array Nat) := #[#[1, 2, 3], #[4]]

-- in a record and a constructor
def pair : Array Nat × Option (Array Nat) := (table, some #[1, 2, 3])

-- an empty array is not shared (it is as short as a name)
def empty1 : Array Nat := #[]
def empty2 : Array Nat := #[]

-- the same numbers at another type: shared where the two are written the same
-- (`[1, 2, 3]` at the preset `pbo`), not where they are not (`Uint8Array.of(1, 2, 3)` at
-- `faithful`)
def bytes : Array UInt8 := #[1, 2, 3]

-- a function returns a fresh array (which a caller owning it may update in place): its body
-- is not rewritten
def fresh (n : Nat) : Array Nat := #[1, 2, 3].push n

def freshConst (_ : Nat) : Array Nat := #[1, 2, 3]

-- a constant after a function still reads `table`
def later : Array (Array Nat) := #[#[4], #[1, 2, 3]]
