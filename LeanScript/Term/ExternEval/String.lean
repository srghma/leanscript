module

public import LeanScript.Term.Extern

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs: strings

The value of every entry of the families of `LeanScript.LeanInitPureExterns.String`, at the
instantiation of the catalogue to the types of the language (`LeanScript.Extern`), on the
values of its arguments: the Lean function the entry stands for.

The arguments are first bound at their Lean types, so the Lean function elaborates as in
Lean.  A `Float` is the `HashableFloat` of the language: an argument is its underlying
float and a result is normalised (`HashableFloat.normalize`).  A function that returns
`Decidable p` answers `decide p` (`ExternBool`).  A proof that the Lean function takes is
erased by the language, so it is decided on the values of the arguments; when it does not
hold (which never happens in a term translated from a Lean program, which had to prove it)
the answer is a default value.
-/

namespace LeanScript

/-- The value of an entry of `StringBootstrapExtern` on the values of its arguments. -/
def StringBootstrapExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StringBootstrapExtern (MyTy := Ty ks) (fun a b => Ty.fn a b) Ty.fn2 σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_string_utf8_get__String_Internal_get, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Internal.get x1 x2 : Char)
  | _, _, .lean_string_trim, x1 =>
    let x1 : String := x1
    (String.Internal.trim x1 : String)
  | _, _, .lean_substring_drop, (x1, x2) =>
    let x1 : Substring.Raw := x1
    let x2 : Nat := x2
    (Substring.Raw.Internal.drop x1 x2 : Substring.Raw)
  | _, _, .lean_substring_prev, (x1, x2) =>
    let x1 : Substring.Raw := x1
    let x2 : String.Pos.Raw := x2
    (Substring.Raw.Internal.prev x1 x2 : String.Pos.Raw)
  | _, _, .lean_substring_extract, (x1, x2, x3) =>
    let x1 : Substring.Raw := x1
    let x2 : String.Pos.Raw := x2
    let x3 : String.Pos.Raw := x3
    (Substring.Raw.Internal.extract x1 x2 x3 : Substring.Raw)
  | _, _, .lean_string_foldl, (x1, x2, x3) =>
    let x1 : String → Char → String := x1
    let x2 : String := x2
    let x3 : String := x3
    (String.Internal.foldl x1 x2 x3 : String)
  | _, _, .lean_substring_tostring, x1 =>
    let x1 : Substring.Raw := x1
    (Substring.Raw.Internal.toString x1 : String)
  | _, _, .lean_string_append__String_Internal_append, (x1, x2) =>
    let x1 : String := x1
    let x2 : String := x2
    (String.Internal.append x1 x2 : String)
  | _, _, .lean_string_get_byte_fast__String_Internal_getUTF8Byte, (s, n) =>
    let s : String := s
    let n : Nat := n
    if h : n < s.utf8ByteSize then (String.Internal.getUTF8Byte s n h : UInt8) else (default : UInt8)
  | _, _, .lean_string_isempty, x1 =>
    let x1 : String := x1
    ExternBool.toBool (String.Internal.isEmpty x1)
  | _, _, .lean_string_push, (x1, x2) =>
    let x1 : String := x1
    let x2 : Char := x2
    (String.push x1 x2 : String)
  | _, _, .lean_string_isprefixof, (x1, x2) =>
    let x1 : String := x1
    let x2 : String := x2
    ExternBool.toBool (String.Internal.isPrefixOf x1 x2)
  | _, _, .lean_string_dropright, (x1, x2) =>
    let x1 : String := x1
    let x2 : Nat := x2
    (String.Internal.dropRight x1 x2 : String)
  | _, _, .lean_substring_takewhile, (x1, x2) =>
    let x1 : Substring.Raw := x1
    let x2 : Char → Bool := x2
    (Substring.Raw.Internal.takeWhile x1 x2 : Substring.Raw)
  | _, _, .lean_substring_get, (x1, x2) =>
    let x1 : Substring.Raw := x1
    let x2 : String.Pos.Raw := x2
    (Substring.Raw.Internal.get x1 x2 : Char)
  | _, _, .lean_string_contains, (x1, x2) =>
    let x1 : String := x1
    let x2 : Char := x2
    ExternBool.toBool (String.Internal.contains x1 x2)
  | _, _, .lean_string_front, x1 =>
    let x1 : String := x1
    (String.Internal.front x1 : Char)
  | _, _, .lean_string_posof, (x1, x2) =>
    let x1 : String := x1
    let x2 : Char := x2
    (String.Internal.posOf x1 x2 : String.Pos.Raw)
  | _, _, .lean_substring_all, (x1, x2) =>
    let x1 : Substring.Raw := x1
    let x2 : Char → Bool := x2
    ExternBool.toBool (Substring.Raw.Internal.all x1 x2)
  | _, _, .lean_string_intercalate, (x1, x2) =>
    let x1 : String := x1
    let x2 : List String := x2
    (String.Internal.intercalate x1 x2 : String)
  | _, _, .lean_string_drop, (x1, x2) =>
    let x1 : String := x1
    let x2 : Nat := x2
    (String.Internal.drop x1 x2 : String)
  | _, _, .lean_string_length__String_Internal_length, x1 =>
    let x1 : String := x1
    (String.Internal.length x1 : Nat)
  | _, _, .lean_string_utf8_at_end__String_Internal_atEnd, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    ExternBool.toBool (String.Internal.atEnd x1 x2)
  | _, _, .lean_substring_beq, (x1, x2) =>
    let x1 : Substring.Raw := x1
    let x2 : Substring.Raw := x2
    ExternBool.toBool (Substring.Raw.Internal.beq x1 x2)
  | _, _, .lean_string_nextwhile, (x1, x2, x3) =>
    let x1 : String := x1
    let x2 : Char → Bool := x2
    let x3 : String.Pos.Raw := x3
    (String.Internal.nextWhile x1 x2 x3 : String.Pos.Raw)
  | _, _, .lean_string_utf8_next__String_Internal_next, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Internal.next x1 x2 : String.Pos.Raw)
  | _, _, .lean_string_mk__String_mk, x1 =>
    let x1 : List Char := x1
    (String.ofList x1 : String) -- `String.mk` is deprecated: `String.ofList` is the same function
  | _, _, .lean_string_any, (x1, x2) =>
    let x1 : String := x1
    let x2 : Char → Bool := x2
    ExternBool.toBool (String.Internal.any x1 x2)
  | _, _, .lean_string_pushn, (x1, x2, x3) =>
    let x1 : String := x1
    let x2 : Char := x2
    let x3 : Nat := x3
    (String.Internal.pushn x1 x2 x3 : String)
  | _, _, .lean_string_capitalize, x1 =>
    let x1 : String := x1
    (String.Internal.capitalize x1 : String)
  | _, _, .lean_string_utf8_extract__String_Internal_extract, (x1, x2, x3) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    let x3 : String.Pos.Raw := x3
    (String.Internal.extract x1 x2 x3 : String)
  | _, _, .lean_string_pos_min, (x1, x2) =>
    let x1 : String.Pos.Raw := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.Internal.min x1 x2 : String.Pos.Raw)
  | _, _, .lean_substring_front, x1 =>
    let x1 : Substring.Raw := x1
    (Substring.Raw.Internal.front x1 : Char)
  | _, _, .lean_string_pos_sub, (x1, x2) =>
    let x1 : String.Pos.Raw := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.Internal.sub x1 x2 : String.Pos.Raw)
  | _, _, .lean_substring_isempty, x1 =>
    let x1 : Substring.Raw := x1
    ExternBool.toBool (Substring.Raw.Internal.isEmpty x1)
  | _, _, .lean_string_offsetofpos, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Internal.offsetOfPos x1 x2 : Nat)

/-- The value of an entry of `StringPosRawExtern` on the values of its arguments. -/
def StringPosRawExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StringPosRawExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_string_get_byte_fast__String_getUtf8Byte, (s, p) =>
    let s : String := s
    let p : String.Pos.Raw := p
    if h : p < s.rawEndPos then (String.getUTF8Byte s p h : UInt8) else (default : UInt8)
  | _, _, .lean_string_get_byte_fast__String_getUTF8Byte, (s, p) =>
    let s : String := s
    let p : String.Pos.Raw := p
    if h : p < s.rawEndPos then (String.getUTF8Byte s p h : UInt8) else (default : UInt8)

/-- The value of an entry of `StringDefsExtern` on the values of its arguments. -/
def StringDefsExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StringDefsExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_string_append__String_append, (x1, x2) =>
    let x1 : String := x1
    let x2 : String := x2
    (String.append x1 x2 : String)

/-- The value of an entry of `StringBasicExtern` on the values of its arguments. -/
def StringBasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StringBasicExtern (MyTy := Ty ks) (fun t => Ty.option t) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_string_utf8_next__String_next, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.next x1 x2 : String.Pos.Raw)
  | _, _, .lean_string_utf8_next__String_Pos_Raw_next, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.next x1 x2 : String.Pos.Raw)
  | _, _, .lean_string_utf8_get__String_Pos_Raw_get, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.get x1 x2 : Char)
  | _, _, .lean_string_utf8_get__String_get, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.get x1 x2 : Char)
  | _, _, .lean_string_utf8_get_opt__String_Pos_Raw_get?, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.get? x1 x2 : Option Char)
  | _, _, .lean_string_utf8_get_opt__String_get?, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.get? x1 x2 : Option Char)
  | _, _, .lean_string_utf8_prev__String_Pos_Raw_prev, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.prev x1 x2 : String.Pos.Raw)
  | _, _, .lean_string_utf8_prev__String_prev, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.prev x1 x2 : String.Pos.Raw)
  | _, _, .lean_string_utf8_next_fast__String_next', (s, p) =>
    let s : String := s
    let p : String.Pos.Raw := p
    if h : ¬String.Pos.Raw.atEnd s p = Bool.true then (String.Pos.Raw.next' s p h : String.Pos.Raw) else (default : String.Pos.Raw)
  | _, _, (.lean_string_utf8_next_fast__String_Pos_next s _), pos =>
    let pos : String.Pos s := pos
    if h : pos ≠ s.endPos then (String.Pos.next pos h : String.Pos s) else (default : String.Pos s)
  | _, _, .lean_string_data__String_data, x1 =>
    let x1 : String := x1
    (String.toList x1 : List Char) -- `String.data` is deprecated: `String.toList` is the same function
  | _, _, .lean_string_data__String_toList, x1 =>
    let x1 : String := x1
    (String.toList x1 : List Char)
  | _, _, (.lean_string_utf8_extract_fast s _), (x1, x2) =>
    let x1 : String.Pos s := x1
    let x2 : String.Pos s := x2
    (String.extract x1 x2 : String)
  | _, _, .lean_string_utf8_at_end__String_atEnd, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    ExternBool.toBool (String.Pos.Raw.atEnd x1 x2)
  | _, _, .lean_string_utf8_at_end__String_Pos_Raw_atEnd, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    ExternBool.toBool (String.Pos.Raw.atEnd x1 x2)
  | _, _, .lean_string_utf8_get_bang__String_Pos_Raw_get!, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.get! x1 x2 : Char)
  | _, _, .lean_string_utf8_get_bang__String_get!, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    (String.Pos.Raw.get! x1 x2 : Char)
  | _, _, .lean_string_utf8_get_fast__String_get', (s, p) =>
    let s : String := s
    let p : String.Pos.Raw := p
    if h : ¬String.Pos.Raw.atEnd s p = Bool.true then (String.Pos.Raw.get' s p h : Char) else (default : Char)
  | _, _, .lean_string_utf8_get_fast__String_Pos_Raw_get', (s, p) =>
    let s : String := s
    let p : String.Pos.Raw := p
    if h : ¬String.Pos.Raw.atEnd s p = Bool.true then (String.Pos.Raw.get' s p h : Char) else (default : Char)
  | _, _, .lean_string_is_valid_pos, (x1, x2) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    ExternBool.toBool (String.Pos.Raw.isValid x1 x2)
  | _, _, .lean_string_dec_lt, (x1, x2) =>
    let x1 : String := x1
    let x2 : String := x2
    ExternBool.toBool (String.decidableLT x1 x2)
  | _, _, .lean_string_utf8_extract__String_Pos_Raw_extract, (x1, x2, x3) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    let x3 : String.Pos.Raw := x3
    (String.Pos.Raw.extract x1 x2 x3 : String)

/-- The value of an entry of `StringLengthExtern` on the values of its arguments. -/
def StringLengthExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StringLengthExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_string_length__String_length, x1 =>
    let x1 : String := x1
    (String.length x1 : Nat)

/-- The value of an entry of `StringPatternExtern` on the values of its arguments. -/
def StringPatternExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StringPatternExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_string_memcmp, (lhs, rhs, lstart, rstart, len) =>
    let lhs : String := lhs
    let rhs : String := rhs
    let lstart : String.Pos.Raw := lstart
    let rstart : String.Pos.Raw := rstart
    let len : String.Pos.Raw := len
    if h0 : len.offsetBy lstart ≤ lhs.rawEndPos then if h1 : len.offsetBy rstart ≤ rhs.rawEndPos then ExternBool.toBool (String.Slice.Pattern.Internal.memcmpStr lhs rhs lstart rstart len h0 h1) else (default : Bool) else (default : Bool)

/-- The value of an entry of `StringSliceExtern` on the values of its arguments. -/
def StringSliceExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StringSliceExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_slice_dec_lt, (x1, x2) =>
    let x1 : String.Slice := x1
    let x2 : String.Slice := x2
    ExternBool.toBool (String.Slice.instDecidableLt x1 x2)
  | _, _, .lean_slice_hash, x1 =>
    let x1 : String.Slice := x1
    (String.Slice.hash x1 : UInt64)

/-- The value of an entry of `StringModifyExtern` on the values of its arguments. -/
def StringModifyExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StringModifyExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_string_utf8_set__String_Pos_Raw_set, (x1, x2, x3) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    let x3 : Char := x3
    (String.Pos.Raw.set x1 x2 x3 : String)
  | _, _, (.lean_string_utf8_set__String_Pos_set s _), (p, x2) =>
    let p : String.Pos s := p
    let x2 : Char := x2
    if h0 : p ≠ s.endPos then (String.Pos.set p x2 h0 : String) else (default : String)
  | _, _, .lean_string_utf8_set__String_set, (x1, x2, x3) =>
    let x1 : String := x1
    let x2 : String.Pos.Raw := x2
    let x3 : Char := x3
    (String.Pos.Raw.set x1 x2 x3 : String)

/-- The value of an entry of `OrdStringExtern` on the values of its arguments. -/
def OrdStringExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    OrdStringExtern (MyTy := Ty ks) Ty.ordering σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_string_compare, (x1, x2) =>
    let x1 : String := x1
    let x2 : String := x2
    orderingToFin (String.compare x1 x2)

end LeanScript

end
