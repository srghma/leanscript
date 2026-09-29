module

prelude
public import Init.Prelude
public import Init.Data.Format.Basic
public import Init.Data.Format.Instances
public import Init.Data.ToString.Basic
public import Init.LawfulBEqTactics
public import Init.Core
public import Init.Data.Bool

@[expose] public section

namespace LeanScript

open Std (Format ToFormat)

/-!
# `LeanPrimTyCovariant`: the leaf type formers

The type formers of the language that are covariant in the types they take — arrays, lists,
thunks, lazy values, hash maps and hash sets — with the children abstracted, so the same former
serves `Ty` and the backends.

**Hash maps and hash sets.**  `hashMap κ ν` is `Std.HashMap κ ν` and `hashSet κ` is
`Std.HashSet κ`.  They are formers of their own (and not their unfolding, a structure around an
array of association lists) because the backend compiles them to what JavaScript has:

* a key of a leaf type whose values are told apart by their `String(·)` rendering
  (`LeanPrimTy.isObjectKey`: every leaf but `substringRaw`, `stringSlice` and the float
  models) or of an enum (whose values are small integers) is a property name, so the map is a
  JavaScript object (`Object.create(null)`, or a `Map`, whichever the backend prefers) and the
  set an object of `true`s (or a `Set`); the `BEq`/`Hashable` instances are not needed at run
  time, the key is converted with `String`;
* any other key is hashed with the `Hashable` instance and compared with the `BEq` instance of
  the program, so the map is a JavaScript `Map` from the hash to the bucket of entries with
  that hash, and the operations take the two instances as functions (as `Array.contains` takes
  `BEq.beq`, see `LeanScript.LeanInitPureExterns.HashMap`).

A hash map has two children (the keys and the values), so `LeanPrimTyCovariant` is covariant in
each of them: `map` maps both.
-/

/-- A leaf type former with one covariant argument of type `α`. -/
inductive LeanPrimTyCovariant (α : Type) where
  /-- Always a JS array. -/
  | array : α → LeanPrimTyCovariant α
  /-- A Lean `List`. -/
  | list : α → LeanPrimTyCovariant α
  -- -- /-- In JS: `Promise<α>` (async task / worker). -/
  -- | task : α → LeanPrimTyCovariant α
  -- -- /-- In JS: `Promise<α>`. -/
  -- | promise : α → LeanPrimTyCovariant α
  /-- In JS: `(fn) => { let r; return () => (r === undefined ? (r = fn()) : r); }`. -/
  | thunk : α → LeanPrimTyCovariant α
  /-- In JS: `() => { return ... }`. -/
  | lazy : α → LeanPrimTyCovariant α
  /-- A Lean `Std.HashMap κ ν` (keys, then values).  In JS: an `Object` (or a `Map`) when the
      key is a leaf of `LeanPrimTy.isObjectKey` or an enum, keyed by `String(key)`; otherwise a
      `Map` from the hash to a bucket of entries. -/
  | hashMap : α → α → LeanPrimTyCovariant α
  /-- A Lean `Std.HashSet κ`.  In JS: an `Object` of `true`s (or a `Set`) when the key is a leaf
      of `LeanPrimTy.isObjectKey` or an enum, keyed by `String(key)`; otherwise a `Map` from the
      hash to a bucket of keys. -/
  | hashSet : α → LeanPrimTyCovariant α
  -- | shareCommonState : α → LeanPrimTyCovariant α
  deriving Repr, DecidableEq, Inhabited, BEq, ReflBEq, LawfulBEq, Hashable

namespace LeanPrimTyCovariant

/-- The children, in order (a hash map has two: the keys, then the values). -/
def children : LeanPrimTyCovariant α → List α
  | .array a   => [a]
  | .list a    => [a]
  -- | .task a    => [a]
  -- | .promise a => [a]
  | .thunk a   => [a]
  | .lazy a    => [a]
  | .hashMap k v => [k, v]
  | .hashSet k => [k]
  -- | .shareCommonState a    => [a]

/-- Maps a function over the covariant wrapper. -/
def map (f : α → β) : LeanPrimTyCovariant α → LeanPrimTyCovariant β
  | .array a   => .array (f a)
  | .list a    => .list (f a)
  -- | .task a    => .task (f a)
  -- | .promise a => .promise (f a)
  | .thunk a   => .thunk (f a)
  | .lazy a    => .lazy (f a)
  | .hashMap k v => .hashMap (f k) (f v)
  | .hashSet k => .hashSet (f k)
  -- | .shareCommonState a    => .shareCommonState (f a)

instance : Functor LeanPrimTyCovariant where
  map := map

/-- Formats the covariant type into a `Format` document. -/
def format [ToFormat α] : LeanPrimTyCovariant α → Format
  | .array a   => "(array " ++ Std.format a ++ ")"
  | .list a    => "(list " ++ Std.format a ++ ")"
  -- | .task a    => "(task " ++ Std.format a ++ ")"
  -- | .promise a => "(promise " ++ Std.format a ++ ")"
  | .thunk a   => "(thunk " ++ Std.format a ++ ")"
  | .lazy a    => "(lazy " ++ Std.format a ++ ")"
  | .hashMap k v => "(hashMap " ++ Std.format k ++ " " ++ Std.format v ++ ")"
  | .hashSet k => "(hashSet " ++ Std.format k ++ ")"
  -- | .shareCommonState a    => "(shareCommonState " ++ Std.format a ++ ")"

instance [ToFormat α] : ToFormat (LeanPrimTyCovariant α) where
  format := format

instance [ToFormat α] : ToString (LeanPrimTyCovariant α) where
  toString x := toString (format x)

end LeanPrimTyCovariant

end LeanScript

end
