/-!
Two mutually tail-recursive functions whose parameters **disagree** on their types:
`walkStr` takes a `Nat` and a `String`, `walkNat` a `Nat` and a `Nat`.

The merged loop gives them one slot vector, and a slot is shared only where the members
agree on its type (`LakeJs.Compile`, `groupSlotAlloc`), so the loop here has three slots
— `Nat`, `String`, `Nat` — rather than two slots one of which holds values of two types.
Every loop variable therefore has a single type, which is what lets a JavaScript engine
keep it unboxed.
-/

mutual

def walkStr : Nat → String → Nat
  | 0, s => s.length
  | n + 1, s => walkNat n (s.length + 1)

def walkNat : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => walkStr n (if k == 0 then "" else "xy")

end
