module

@[expose] public section

set_option autoImplicit false

/-!
# JavaScript names of Lean names, without collisions

A Lean name may hold any character (`«a.b ?$$ \" →»`), a JavaScript identifier may not.  The
conversion writes the name of an exported function, and of a parameter, as an identifier:

* an ASCII letter or digit is kept (a digit is escaped at the start of a name);
* `_` is kept, unless the next character is `x`, `u` or `U`;
* a character beyond ASCII that the identifier may hold at its place (`idChar`: the Unicode
  properties `ID_Start` / `ID_Continue`) is kept: `α`, `β₁`… stay as they are;
* any other character is escaped by its code point, in hexadecimal digits of a fixed width:
  `_xHH` (below `0x100`), `_uHHHH` (below `0x10000`), `_UHHHHHH` (beyond);
* a reserved word (`class`, `Math`…), and the empty name, get the mark `_x` at the end.

```
«a.b ?$$ \" →»   ⟶   a_x2eb_x20_x3f_x24_x24_x20_x22_x20_u2192
foo'             ⟶   foo_x27
x_x              ⟶   x_x5fx
class            ⟶   class_x
```

The components of a name are joined by `$` (`Foo.bar` is `Foo$bar`), which no component holds.

Unlike a lossy replacement of every other character by `_` (which writes both `a.b` and `a_b`
as `a_b`), or escapes of a varying width without a separator (where `_u2eb` may be `.` then
`b` or the code point `0x2eb`), the encoding can be read back: `decode` gives the name again
(`decode_ident`, `decodeName_name`), so two distinct Lean names never get the same JavaScript
name (`ident_injective`, `name_injective`).
-/

namespace MoreJs.Ident

/-! ## Hexadecimal digits -/

/-- The lowercase hexadecimal digit of `d < 16`. -/
def hexChar (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- The value of a hexadecimal digit written by `hexChar`. -/
def hexVal (c : Char) : Nat := if c.toNat < 58 then c.toNat - 48 else c.toNat - 87

/-- The last `k` hexadecimal digits of `n`, the most significant first. -/
def hexDigits : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, n => hexDigits k (n / 16) ++ [hexChar (n % 16)]

/-- The number written by hexadecimal digits, the most significant first. -/
def readHex (cs : List Char) : Nat := cs.foldl (fun acc c => acc * 16 + hexVal c) 0

/-! ## Encoding -/

/-- The number of hexadecimal digits after the marker `m` of an escape (`_x`, `_u`, `_U`). -/
def escWidth (m : Char) : Option Nat :=
  if m = 'x' then some 2 else if m = 'u' then some 4 else if m = 'U' then some 6 else none

/-- A character written by its code point. -/
def escapeChar (c : Char) : List Char :=
  if c.toNat < 0x100 then '_' :: 'x' :: hexDigits 2 c.toNat
  else if c.toNat < 0x10000 then '_' :: 'u' :: hexDigits 4 c.toNat
  else '_' :: 'U' :: hexDigits 6 c.toNat

/-- Whether the character `c` (the first of the name when `first`), followed by `next`, is
    written as it is.  `idChar first c` decides the characters beyond ASCII. -/
def keepChar (idChar : Bool → Char → Bool) (first : Bool) (c : Char) (next : Option Char) :
    Bool :=
  if c = '_' then (next.bind escWidth).isNone
  else if c.toNat < 128 then c.isAlpha || (c.isDigit && !first)
  else idChar first c

/-- The characters of a name, each kept or escaped. -/
def encode (idChar : Bool → Char → Bool) : Bool → List Char → List Char
  | _, [] => []
  | first, c :: cs =>
    (if keepChar idChar first c cs.head? then [c] else escapeChar c) ++ encode idChar false cs

/-- The characters of the identifier of a name (one component): its encoding, with the mark
    `_x` when it is empty or a reserved word. -/
def identChars (idChar : Bool → Char → Bool) (reserved : String → Bool) (s : String) :
    List Char :=
  let e := encode idChar true s.toList
  if s.toList.isEmpty || reserved (String.ofList e) then e ++ ['_', 'x'] else e

/-- The identifier of a name (one component, or a parameter). -/
def ident (idChar : Bool → Char → Bool) (reserved : String → Bool) (s : String) : String :=
  String.ofList (identChars idChar reserved s)

/-- The identifier of a name of several components: their identifiers joined by `$` (a name
    holding a `$` is never a reserved word: only a name of one component is checked). -/
def name (idChar : Bool → Char → Bool) (reserved : String → Bool) (cs : List String) :
    String :=
  match cs with
  | [c] => ident idChar reserved c
  | cs => String.ofList (List.intercalate ['$'] (cs.map (identChars idChar fun _ => false)))

/-! ## Decoding -/

/-- The characters of a name, read back from its identifier. -/
def decode (l : List Char) : List Char :=
  match l with
  | [] => []
  | c :: rest =>
    if c = '_' then
      match rest with
      | [] => ['_']
      | m :: rest' =>
        match escWidth m with
        | some k =>
          if rest' = [] ∧ m = 'x' then []
          else Char.ofNat (readHex (rest'.take k)) :: decode (rest'.drop k)
        | none => '_' :: decode (m :: rest')
    else c :: decode rest
termination_by l.length
decreasing_by all_goals simp_wf; all_goals (try simp); all_goals omega

/-- The pieces of a list between its `$`s. -/
def splitDollar : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    if c = '$' then [] :: splitDollar rest
    else match splitDollar rest with
      | x :: xs => (c :: x) :: xs
      | [] => [[c]]

/-- The components of a name, read back from its identifier. -/
def decodeName (s : String) : List String :=
  (splitDollar s.toList).map fun p => String.ofList (decode p)

/-! ## Reading back -/

theorem hexVal_hexChar : ∀ d, d < 16 → hexVal (hexChar d) = d := by decide

theorem hexChar_ne_dollar : ∀ d, d < 16 → hexChar d ≠ '$' := by decide

theorem length_hexDigits (k n : Nat) : (hexDigits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [hexDigits, ih]

theorem readHex_append (l : List Char) (c : Char) :
    readHex (l ++ [c]) = readHex l * 16 + hexVal c := by
  simp [readHex, List.foldl_append]

theorem readHex_hexDigits (k n : Nat) : readHex (hexDigits k n) = n % 16 ^ k := by
  induction k generalizing n with
  | zero => simp [hexDigits, readHex, Nat.mod_one]
  | succ k ih =>
    rw [hexDigits, readHex_append, ih, hexVal_hexChar _ (Nat.mod_lt _ (by decide)),
      Nat.pow_succ, Nat.mul_comm (16 ^ k) 16, Nat.mod_mul]
    omega

theorem mem_hexDigits {k n : Nat} {c : Char} (h : c ∈ hexDigits k n) :
    ∃ d, d < 16 ∧ c = hexChar d := by
  induction k generalizing n with
  | zero => simp [hexDigits] at h
  | succ k ih =>
    simp only [hexDigits, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact ih h
    · exact ⟨_, Nat.mod_lt _ (by decide), h⟩

theorem decode_nil : decode [] = [] := by rw [decode.eq_def]

theorem decode_cons_of_ne {c : Char} (h : c ≠ '_') (rest : List Char) :
    decode (c :: rest) = c :: decode rest := by
  rw [decode.eq_def]; simp [h]

theorem decode_mark : decode ['_', 'x'] = [] := by
  rw [decode.eq_def]; simp [escWidth]

/-- A `_` followed by neither `x`, `u` nor `U` is read as itself. -/
theorem decode_underscore {l : List Char} (h : ∀ m r, l = m :: r → escWidth m = none) :
    decode ('_' :: l) = '_' :: decode l := by
  cases l with
  | nil => rw [decode.eq_def]; simp [decode_nil]
  | cons m r =>
    rw [decode.eq_def]
    simp [h m r rfl]

theorem decode_escape_eq {m : Char} {k : Nat} {rest : List Char} (hm : escWidth m = some k)
    (hne : rest ≠ []) :
    decode ('_' :: m :: rest) = Char.ofNat (readHex (rest.take k)) :: decode (rest.drop k) := by
  rw [decode.eq_def]; simp [hm, hne]

/-- The escape of a character is read back as the character. -/
theorem decode_escape (c : Char) (t : List Char) :
    decode (escapeChar c ++ t) = c :: decode t := by
  have hc : c.toNat < 0x110000 := by
    have := c.valid
    simp only [UInt32.isValidChar, Nat.isValidChar] at this
    simp only [Char.toNat]
    omega
  have key : ∀ (m : Char) (k : Nat), escWidth m = some k → 0 < k → c.toNat < 16 ^ k →
      decode ('_' :: m :: (hexDigits k c.toNat ++ t)) = c :: decode t := by
    intro m k hm hk0 hk
    have hne : hexDigits k c.toNat ++ t ≠ [] := by
      intro h
      have := congrArg List.length h
      simp [length_hexDigits] at this
      omega
    rw [decode_escape_eq hm hne]
    have h1 : (hexDigits k c.toNat ++ t).take k = hexDigits k c.toNat := by
      simp [length_hexDigits]
    have h2 : (hexDigits k c.toNat ++ t).drop k = t := by
      simp [length_hexDigits]
    rw [h1, h2, readHex_hexDigits, Nat.mod_eq_of_lt hk, Char.ofNat_toNat]
  unfold escapeChar
  split
  · exact key 'x' 2 rfl (by decide) (by simp; omega)
  · split
    · exact key 'u' 4 rfl (by decide) (by simp; omega)
    · exact key 'U' 6 rfl (by decide) (by simp; omega)

/-- The encoding starts with its first character, or with the `_` of an escape. -/
theorem encode_head (idChar : Bool → Char → Bool) (b : Bool) (c : Char) (cs : List Char) :
    ∃ r, encode idChar b (c :: cs) = c :: r ∨ encode idChar b (c :: cs) = '_' :: r := by
  simp only [encode]
  split
  · exact ⟨_, Or.inl rfl⟩
  · unfold escapeChar
    split
    · exact ⟨_, Or.inr rfl⟩
    · split
      · exact ⟨_, Or.inr rfl⟩
      · exact ⟨_, Or.inr rfl⟩

/-- The encoding of a name, followed by anything that does not start with `x`, `u` or `U`, is
    read back as the name followed by the reading of the rest. -/
theorem decode_encode_append (idChar : Bool → Char → Bool) (cs : List Char) (b : Bool)
    (t : List Char) (ht : (t.head?.bind escWidth).isNone) :
    decode (encode idChar b cs ++ t) = cs ++ decode t := by
  induction cs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    simp only [encode, List.append_assoc]
    split
    · next hk =>
      simp only [List.nil_append, List.cons_append]
      by_cases hc : c = '_'
      · subst hc
        simp only [keepChar, ite_true] at hk
        rw [decode_underscore, ih]
        intro m r heq
        cases cs with
        | nil =>
          simp only [encode, List.nil_append] at heq
          subst heq
          simpa [Option.isNone_iff_eq_none] using ht
        | cons c' cs' =>
          obtain ⟨r', hr | hr⟩ := encode_head idChar false c' cs'
          · rw [hr] at heq
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, -⟩ := heq
            simpa [Option.isNone_iff_eq_none] using hk
          · rw [hr] at heq
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, -⟩ := heq
            rfl
      · rw [decode_cons_of_ne hc, ih]
    · rw [decode_escape, ih]
      rfl

theorem decode_encode (idChar : Bool → Char → Bool) (cs : List Char) (b : Bool) :
    decode (encode idChar b cs) = cs := by
  have := decode_encode_append idChar cs b [] rfl
  simpa [decode_nil] using this

theorem decode_ident (idChar : Bool → Char → Bool) (reserved : String → Bool) (s : String) :
    decode (identChars idChar reserved s) = s.toList := by
  unfold identChars
  dsimp only
  split
  · rw [decode_encode_append idChar _ true _ rfl, decode_mark, List.append_nil]
  · exact decode_encode idChar _ true

/-- Two names with the same identifier are the same name. -/
theorem ident_injective (idChar : Bool → Char → Bool) (reserved : String → Bool) (s t : String)
    (h : ident idChar reserved s = ident idChar reserved t) : s = t := by
  have h' : identChars idChar reserved s = identChars idChar reserved t := by
    have := congrArg String.toList h
    simpa [ident] using this
  have := congrArg decode h'
  rw [decode_ident, decode_ident] at this
  exact String.toList_inj.mp this

/-! ## Names of several components -/

theorem dollar_not_mem_encode (idChar : Bool → Char → Bool) (b : Bool) (cs : List Char) :
    '$' ∉ encode idChar b cs := by
  induction cs generalizing b with
  | nil => simp [encode]
  | cons c cs ih =>
    simp only [encode, List.mem_append, not_or]
    refine ⟨?_, ih false⟩
    split
    · next hk =>
      simp only [List.mem_singleton]
      intro h
      subst h
      simp [keepChar] at hk
    · unfold escapeChar
      intro h
      repeat' split at h
      all_goals
        simp only [List.mem_cons] at h
        rcases h with h | h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · obtain ⟨d, hd, hd'⟩ := mem_hexDigits h
          exact hexChar_ne_dollar d hd hd'.symm

theorem dollar_not_mem_identChars (idChar : Bool → Char → Bool) (reserved : String → Bool)
    (s : String) : '$' ∉ identChars idChar reserved s := by
  have := dollar_not_mem_encode idChar true s.toList
  simp only [identChars]
  split <;> simp_all

theorem splitDollar_of_not_mem (a : List Char) (h : '$' ∉ a) : splitDollar a = [a] := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [splitDollar, Ne.symm h.1, ite_false, ih h.2]

theorem splitDollar_append (a b : List Char) (h : '$' ∉ a) :
    splitDollar (a ++ '$' :: b) = a :: splitDollar b := by
  induction a with
  | nil => simp [splitDollar]
  | cons c a ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.cons_append, splitDollar, Ne.symm h.1, ite_false, ih h.2]

theorem splitDollar_intercalate (ps : List (List Char)) (hne : ps ≠ [])
    (h : ∀ p ∈ ps, '$' ∉ p) : splitDollar (List.intercalate ['$'] ps) = ps := by
  induction ps with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    cases ps with
    | nil =>
      simp only [List.intercalate_singleton]
      exact splitDollar_of_not_mem p (h p (by simp))
    | cons q qs =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
        splitDollar_append _ _ (h p (by simp)),
        ih (by simp) (fun r hr => h r (List.mem_cons_of_mem _ hr))]

theorem decodeName_intercalate (idChar : Bool → Char → Bool) (reserved : String → Bool)
    (cs : List String) (hne : cs ≠ []) :
    decodeName (String.ofList (List.intercalate ['$'] (cs.map (identChars idChar reserved)))) =
      cs := by
  unfold decodeName
  rw [String.toList_ofList, splitDollar_intercalate _ (by simpa using hne)]
  · simp only [List.map_map]
    conv => rhs; rw [← List.map_id cs]
    apply List.map_congr_left
    intro s _
    simp [decode_ident]
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨s, -, rfl⟩ := hp
    exact dollar_not_mem_identChars idChar reserved s

/-- The components of a name are read back from its identifier. -/
theorem decodeName_name (idChar : Bool → Char → Bool) (reserved : String → Bool)
    (cs : List String) (hne : cs ≠ []) : decodeName (name idChar reserved cs) = cs := by
  match cs, hne with
  | [c], _ =>
    have := decodeName_intercalate idChar reserved [c] (by simp)
    simpa [name, ident, List.intercalate_singleton] using this
  | [], h => exact absurd rfl h
  | c :: d :: ds, _ =>
    exact decodeName_intercalate idChar (fun _ => false) _ (by simp)

/-- Two names (lists of components, not empty) with the same identifier are the same name. -/
theorem name_injective (idChar : Bool → Char → Bool) (reserved : String → Bool)
    (cs ds : List String) (hc : cs ≠ []) (hd : ds ≠ [])
    (h : name idChar reserved cs = name idChar reserved ds) : cs = ds := by
  rw [← decodeName_name idChar reserved cs hc, ← decodeName_name idChar reserved ds hd, h]

end MoreJs.Ident

end
