module
import Init.Data.Array.Lemmas
import Aesop
public import NonEmpty.DowngradeMap
public import NonEmpty.ArrayUtil

@[expose] public section

-- why this is needed? for https://github.com/leanprover/lean4/issues/4964#issuecomment-4337841019
namespace NonEmpty.ArrayCorrectByConstruction

@[ext]
structure NonEmptyArray (α : Type u) where
  head : α
  tail : Array α
  deriving Hashable, Ord, Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

instance [ToString α] : ToString (NonEmptyArray α) where
  toString a := "#!" ++ toString (#[a.head] ++ a.tail)

instance [Inhabited α] : Inhabited (NonEmptyArray α) where
  default := ⟨default, #[]⟩

namespace NonEmptyArray

@[simp] abbrev toArr (xs : NonEmptyArray α) : Array α :=
  #[xs.head] ++ xs.tail

@[simp] protected def _root_.Array.mapNonEmptyArray (as : Array α) (f : α → NonEmptyArray β) : Array β :=
  as.flatMap (fun a => (f a).toArr)

@[simp] protected theorem _root_.Array.mapNonEmptyArray_id (as : Array (NonEmptyArray α)) :
    as.mapNonEmptyArray id = (as.map toArr).flatten := by
  simp only [Array.mapNonEmptyArray, Array.flatMap_def, id_def]

@[simp] abbrev size (xs : NonEmptyArray α) : Nat := 1 + xs.tail.size

-- @[inline_if_reduce] abbrev getElem (as : NonEmptyArray α) (i : Nat) (h : i < as.size) : α :=
--   match i with
--   | 0 => as.head
--   | n + 1 =>
--     have : n < as.tail.size := by
--       -- h is n + 1 < size xs
--       -- size xs is 1 + xs.tail.size
--       simp only [size] at h
--       omega
--     as.tail[n]'this

-- @[always_inline] abbrev getElem? (as : NonEmptyArray α) (i : Nat) : Option α :=
--   if h : i < as.size then some (as.getElem i h) else none

instance : GetElem (NonEmptyArray α) Nat α (fun as i => i < as.size) where
  getElem as i h :=
    match i with
  | 0 => as.head
  | n + 1 =>
    have : n < as.tail.size := by
      -- h is n + 1 < size xs
      -- size xs is 1 + xs.tail.size
      simp only [size] at h
      omega
    as.tail[n]'this

instance : GetElem? (NonEmptyArray α) Nat α (fun as i => i < as.size) where
  getElem? as i := if h : i < as.size then as[i]'h else none

-- @[simp] theorem getElem?_def (as : NonEmptyArray α) (i : Nat) [Decidable (i < as.size)] :
--     as[i]? = if h : i < as.size then some as[i] else none := by
--   simp_all only [size]
--   split
--   next h => simp_all only [size, getElem?_pos]
--   next h => simp_all only [Nat.not_lt, size, getElem?_neg]

-- @[simp] theorem getElem!_def [Inhabited α] (as : NonEmptyArray α) (i : Nat) :
--     as[i]! = match as[i]? with | some e => e | none => default := rfl

-- @[simp] theorem getElem!_def_if [Inhabited α] (as : NonEmptyArray α) (i : Nat) [Decidable (i < as.size)] :
--     as[i]! = if h : i < as.size then as[i] else default := by
--   simp_all only [size, getElem!_def, getElem?_def]
--   split
--   next x e heq =>
--     simp_all only [Option.dite_none_right_eq_some, Option.some.injEq]
--     obtain ⟨w, h⟩ := heq
--     subst h
--     simp_all only [↓reduceDIte]
--   next x heq =>
--     simp_all only [dif_neg_iff, reduceCtorEq, imp_false, Nat.not_lt, right_eq_dite_iff]
--     intro h
--     grind only

instance : LawfulGetElem (NonEmptyArray α) Nat α (fun as i => i < as.size) where
  -- getElem?_def := getElem?_def
  -- getElem!_def := getElem!_def

@[simp] theorem size_toArr (as : NonEmptyArray α) : as.toArr.size = as.size := by
  simp only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, size]

@[simp] theorem toArr_getElem (as : NonEmptyArray α) (i : Nat) (h : i < as.size) :
    as.toArr[i]'(by simp only [size_toArr]; exact h) = as[i] := by
  simp only [GetElem.getElem];
  simp_all only [toArr, Array.getInternal_eq_getElem, size]
  split
  next i h h_1 =>
    simp_all only [size, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one,
      Array.getElem_append_left, List.getElem_toArray, List.getElem_cons_zero]
  next i h n h_1 =>
    simp_all only [size, Nat.succ_eq_add_one, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.le_add_left, Array.getElem_append_right, Nat.add_one_sub_one]

@[simp] theorem getElem?_eq_toArr_getElem? (as : NonEmptyArray α) (i : Nat) :
    as[i]? = as.toArr[i]? := by
  rw [getElem?_def]
  split
  · next h =>
    have h' : i < as.toArr.size := by simp only [toArr, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, h]
    rw [getElem?_pos as.toArr i h', toArr_getElem]
  · next h =>
    have h' : ¬i < as.toArr.size := by simp only [toArr, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, h, not_false_eq_true]
    rw [getElem?_neg as.toArr i h']

@[simp] abbrev fromArray? (xs : Array α) : Option (NonEmptyArray α) :=
  if h : xs.size > 0 then some ⟨xs[0]'h, xs[1:]⟩ else none

@[simp] abbrev fromArray! [Inhabited α] (xs : Array α) : NonEmptyArray α :=
  match fromArray? xs with
  | some xs => xs
  | none => panic! "Expected non-empty array"

@[simp] abbrev cons (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  ⟨a, #[xs.head] ++ xs.tail⟩

@[simp] abbrev map (f : α → β) (xs : NonEmptyArray α) : NonEmptyArray β :=
  ⟨f xs.head, xs.tail.map f⟩

@[simp] def flatten (xs : NonEmptyArray (NonEmptyArray α)) : NonEmptyArray α :=
  let ⟨h, t⟩ := xs
  ⟨h.head, h.tail ++ t.mapNonEmptyArray id⟩

-- not needed ever
-- @[simp] def foldl (f : β → α → β) (init : β) (xs : NonEmptyArray α) : β :=
--   xs.tail.foldl f (f init xs.head)

@[inline]
def foldlM1 [Monad m] (f : β → α → m β) (g : α → m β) (as : NonEmptyArray α) : m β := do
  as.tail.foldlM f (← g as.head)

def foldrM1 [Monad m] (f : α → β → m β) (g : α → m β) (as : NonEmptyArray α) : m β := do
  let sz := as.tail.size
  if h : 0 < sz then
    -- Use the last element of the tail as the initial seed.
    -- .back h is a safe way to get as.tail[sz-1]
    let init ← g (as.tail.back h)
    -- foldrM with start := sz - 1 begins folding from index sz - 2 down to 0.
    let accumulated ← as.tail.foldrM f init (start := sz - 1)
    -- Combine the result with the head
    f as.head accumulated
  else
    -- Tail is empty, just transform the head
    g as.head

@[simp, inline] def foldl1 (f : b -> a -> b) (g : a -> b) (as : NonEmptyArray a) : b :=
  as.tail.foldl f (g as.head)

/--
Pure right fold for non-empty arrays.
`foldr1 f g [a, b, c]` is `f a (f b (g c))`
-/
@[inline]
def foldr1 (f : α → β → β) (g : α → β) (as : NonEmptyArray α) : β :=
  Id.run <| as.foldrM1 (fun a b => pure (f a b)) (fun a => pure (g a))

@[simp] def mapM [Monad m] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) := do
  return ⟨← f as.head, ← as.tail.mapM f⟩

def mapM' [Monad m] (f : α → m β) (as : NonEmptyArray α) :
    m { bs : NonEmptyArray β // bs.size = as.size } := do
  let tail ← as.tail.mapM' f
  return ⟨⟨← f as.head, tail⟩, by
    simp_all only [size, Nat.add_left_cancel_iff]
    obtain ⟨val, property⟩ := tail
    simp_all only
  ⟩


@[simp] def mapFinIdxM [Monad m] (as : NonEmptyArray α) (f : (i : Nat) → α → (h : i < as.size) → m β) : m (NonEmptyArray β) :=
  return ⟨← f 0 as.head (by simp only [size]; omega),
          ← as.tail.mapFinIdxM (fun i a h => f (i + 1) a (by simp only [size] at h ⊢; omega))⟩

@[simp] def mapIdxM [Monad m] (f : Nat → α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) :=
  as.mapFinIdxM (fun i a _ => f i a)

/-- Map a function over a NonEmptyArray, passing the index. -/
@[simp] def mapFinIdx (as : NonEmptyArray α) (f : (i : Nat) → α → (h : i < as.size) → β) : NonEmptyArray β :=
  ⟨f 0 as.head (by simp only [size]; omega),
   as.tail.mapFinIdx (fun i a h => f (i + 1) a (by simp only [size] at h ⊢; omega))⟩

/-- Map a function over a NonEmptyArray, passing the index. -/
@[simp] def mapIdx (f : Nat → α → β) (as : NonEmptyArray α) : NonEmptyArray β :=
  ⟨f 0 as.head,
   as.tail.mapIdx (fun i => f (i + 1))⟩


--------------------------------------------------------------------------------
-- API Mapped from standard `Array`
--------------------------------------------------------------------------------

@[simp] def toList (xs : NonEmptyArray α) : List α := xs.head :: xs.tail.toList
def toListAppend (xs : NonEmptyArray α) (l : List α) : List α := xs.toList ++ l

@[simp] def isEmpty (_xs : NonEmptyArray α) : Bool := false

def back (xs : NonEmptyArray α) : α := if h : xs.tail.size > 0 then xs.tail.back h else xs.head
def back! [Inhabited α] (xs : NonEmptyArray α) : α := xs.back
def back? (xs : NonEmptyArray α) : Option α := some xs.back

@[simp] theorem toArr_back (xs : NonEmptyArray α) : xs.toArr.back (by simp only [toArr,
  Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]; omega) = xs.back := by
  obtain ⟨h, t⟩ := xs
  simp only [toArr, Array.back_append, Array.isEmpty_iff, List.back_toArray, List.getLast_singleton,
    back, gt_iff_lt]
  split <;> simp_all only [left_eq_dite_iff, Nat.not_lt, Nat.le_zero_eq, Array.size_eq_zero_iff,
    false_implies, List.size_toArray, List.length_nil, Nat.lt_irrefl, ↓reduceDIte]

@[simp] theorem toArr_back? (xs : NonEmptyArray α) : xs.toArr.back? = xs.back? := by
  obtain ⟨h, t⟩ := xs
  rw [toArr, Array.back?_append, back?, back]
  split
  · next h_size =>
    rw [Array.back?_eq_getElem?, getElem?_pos (c := t) (i := t.size - 1) (h := Nat.sub_lt h_size (by decide))]
    simp only [List.back?_toArray, List.getLast?_singleton, Option.or_some, Option.getD_some,
      Array.back_eq_getElem]
  · next h_size =>
    have : t = #[] := Array.size_eq_zero_iff.1 (by simpa only [Array.size_eq_zero_iff, gt_iff_lt,
      Nat.not_lt, Nat.le_zero_eq] using h_size)
    simp only [this, List.back?_toArray, List.getLast?_nil, List.getLast?_singleton, Option.or_some,
      Option.getD_none]

@[simp] def singleton (a : α) : NonEmptyArray α := ⟨a, #[]⟩

@[simp] theorem _root_.Array.mapNonEmptyArray_singleton (as : Array α) (f : α → β) :
    as.mapNonEmptyArray (fun a => singleton (f a)) = as.map f := by
  simp only [Array.mapNonEmptyArray, toArr, singleton, Array.append_empty,
    ArrayUtil.flatMap_singleton_eq_map]

@[simp] def ofFn {n : Nat} (f : Fin (n + 1) → α) : NonEmptyArray α :=
  ⟨f ⟨0, by omega⟩, Array.ofFn (fun (i : Fin n) => f ⟨i.val + 1, by omega⟩)⟩

@[simp] theorem size_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).size = n + 1 := by
  simp only [size, ofFn, Fin.zero_eta, Array.size_ofFn]; omega

@[simp] theorem getElem_ofFn {n : Nat} (f : Fin (n + 1) → α) (i : Nat) (h : i < (ofFn f).size) :
    (ofFn f)[i] = f ⟨i, by simp only [size, size_ofFn] at h; exact h⟩ := by
  simp only [ofFn, GetElem.getElem]
  simp_all only [Fin.zero_eta, size, Array.getInternal_eq_getElem, Array.getElem_ofFn]
  split
  next i h h_1 => simp_all only [size, Array.size_ofFn, Fin.zero_eta]
  next i h n_1 h_1 => simp_all only [size, Array.size_ofFn, Nat.succ_eq_add_one]

-- Modifications returning NonEmptyArray
def push (xs : NonEmptyArray α) (a : α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail.push a⟩

def set (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i < xs.size) : NonEmptyArray α :=
  if h0 : i = 0 then
    ⟨a, xs.tail⟩
  else
    have : i - 1 < xs.tail.size := by simp only [size] at h; omega
    ⟨xs.head, xs.tail.set (i - 1) a this⟩

def set! (xs : NonEmptyArray α) (i : Nat) (a : α) : NonEmptyArray α :=
  if h : i < xs.size then xs.set i a h else
    have : Inhabited (NonEmptyArray α) := ⟨xs⟩
    panic! "invalid index"

def modify (xs : NonEmptyArray α) (i : Nat) (f : α → α) : NonEmptyArray α :=
  if h : i < xs.size then
    if h0 : i = 0 then ⟨f xs.head, xs.tail⟩
    else
      have : i - 1 < xs.tail.size := by simp only [size] at h; omega
      ⟨xs.head, xs.tail.modify (i - 1) f⟩
  else xs

def modifyM [Monad m] (xs : NonEmptyArray α) (i : Nat) (f : α → m α) : m (NonEmptyArray α) := do
  if h : i < xs.size then
    if h0 : i = 0 then return ⟨← f xs.head, xs.tail⟩
    else
      have : i - 1 < xs.tail.size := by simp only [size] at h; omega
      return ⟨xs.head, ← xs.tail.modifyM (i - 1) f⟩
  else return xs

def swap (xs : NonEmptyArray α) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) : NonEmptyArray α :=
  if h0 : i = 0 ∧ j = 0 then xs
  else if h1 : i = 0 then
    let j' := j - 1; have : j' < xs.tail.size := by simp only [size] at hj; omega
    ⟨xs.tail[j'], xs.tail.set j' xs.head this⟩
  else if h2 : j = 0 then
    let i' := i - 1; have : i' < xs.tail.size := by simp only [size] at hi; omega
    ⟨xs.tail[i'], xs.tail.set i' xs.head this⟩
  else
    let i' := i - 1; have hi' : i' < xs.tail.size := by simp only [size] at hi; omega
    let j' := j - 1; have hj' : j' < xs.tail.size := by simp only [size] at hj; omega
    ⟨xs.head, xs.tail.swap i' j' hi' hj'⟩

def swap! (xs : NonEmptyArray α) (i j : Nat) : NonEmptyArray α :=
  if hi : i < xs.size then
    if hj : j < xs.size then xs.swap i j hi hj
    else
      have : Inhabited (NonEmptyArray α) := ⟨xs⟩
      panic! "invalid index"
  else
    have : Inhabited (NonEmptyArray α) := ⟨xs⟩
    panic! "invalid index"

def swapAt (xs : NonEmptyArray α) (i : Nat) (v : α) (hi : i < xs.size) : α × NonEmptyArray α :=
  (xs[i]'hi, xs.set i v hi)

def swapAt! (xs : NonEmptyArray α) (i : Nat) (v : α) : α × NonEmptyArray α :=
  if hi : i < xs.size then xs.swapAt i v hi
  else
    have : Inhabited (α × NonEmptyArray α) := ⟨(v, xs)⟩
    panic! "invalid index"

def fromArray (xs : Array α) (h : xs.size > 0) : NonEmptyArray α :=
  ⟨xs[0]'h, xs.extract 1 xs.size⟩


@[simp] theorem toArr_fromArray (xs : Array α) (h : xs.size > 0) :
  (fromArray xs h).toArr = xs := by
  simp only [toArr, fromArray]
  have : #[xs[0]] = xs.extract 0 1 := by
    apply Array.ext
    · simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Array.size_extract, Nat.sub_zero]; omega
    · intro i h1 h2
      have : i = 0 := by simp_all only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.lt_one_iff, Array.size_extract, Nat.sub_zero]
      subst i; simp only [List.getElem_toArray, List.getElem_cons_zero, Array.getElem_extract,
        Nat.add_zero]
  rw [this, Array.extract_append_extract]
  simp only [Nat.zero_le, Nat.min_eq_left, Array.extract_eq_self_iff, Array.size_eq_zero_iff,
    true_and]
  omega

@[simp] theorem size_fromArray (xs : Array α) (h : xs.size > 0) :
  (fromArray xs h).size = xs.size := by
  simp_all only [size, fromArray, Array.size_extract, Std.le_refl, Nat.min_eq_left]
  omega

@[simp] theorem getElem_fromArray (xs : Array α) (h : xs.size > 0) (i : Nat) (hi : i < (fromArray xs h).size) :
  (fromArray xs h)[i] = xs[i]'(by simpa only [size, size_fromArray] using hi) := by
  cases i with
  | zero => rfl
  | succ i =>
    have hi' : i + 1 < (fromArray xs h).size := by simpa only [size, size_fromArray] using hi
    let elem := (fromArray xs h)[i + 1]'hi'
    have step : elem = (xs.extract 1)[i]'(by
      simp_all only [size, size_fromArray, Array.size_extract, Std.le_refl, Nat.min_eq_left];
      omega) := rfl
    have : (fromArray xs h)[i + 1] = elem := rfl
    rw [this, step, Array.getElem_extract]
    congr 1; omega

def reverse (xs : NonEmptyArray α) : NonEmptyArray α :=
  let arr := xs.toArr.reverse
  have : arr.size > 0 := by simp only [Array.reverse_append, List.reverse_toArray,
    List.reverse_cons, List.reverse_nil, List.nil_append, Array.append_singleton, Array.size_push,
    Array.size_reverse, gt_iff_lt, Nat.zero_lt_succ, arr]
  fromArray arr this

def append (xs ys : NonEmptyArray α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys.toArr⟩

def appendArray (xs : NonEmptyArray α) (ys : Array α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys⟩

def appendList (xs : NonEmptyArray α) (ys : List α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys.toArray⟩

def insertIdx (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i ≤ xs.size) : NonEmptyArray α :=
  if h0 : i = 0 then
    ⟨a, xs.toArr⟩
  else
    have : i - 1 ≤ xs.tail.size := by simp only [size] at h; omega
    ⟨xs.head, xs.tail.insertIdx (i - 1) a this⟩

def insertIdxIfInBounds (xs : NonEmptyArray α) (i : Nat) (a : α) : NonEmptyArray α :=
  if h : i ≤ xs.size then xs.insertIdx i a h else xs

def replace [BEq α] (xs : NonEmptyArray α) (a b : α) : NonEmptyArray α :=
  if xs.head == a then ⟨b, xs.tail⟩
  else ⟨xs.head, xs.tail.replace a b⟩

def zipWith (f : α → β → γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray γ :=
  ⟨f as.head bs.head, as.tail.zipWith f bs.tail⟩

def zipWithAll (f : Option α → Option β → γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray γ :=
  match fromArray? (as.toArr.zipWithAll f bs.toArr) with
  | some res => res
  | none => ⟨f (some as.head) (some bs.head), #[]⟩

def zipWithM [Monad m] (f : α → β → m γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : m (NonEmptyArray γ) := do
  return ⟨← f as.head bs.head, ← as.tail.zipWithM f bs.tail⟩

def zip (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray (α × β) :=
  as.zipWith Prod.mk bs

def zipIdx (xs : NonEmptyArray α) (start := 0) : NonEmptyArray (α × Nat) :=
  ⟨(xs.head, start), xs.tail.zipIdx (start + 1)⟩

@[simp] theorem toArr_zipIdx (xs : NonEmptyArray α) (start := 0) :
    (xs.zipIdx start).toArr = xs.toArr.zipIdx start := by
  obtain ⟨head, tail⟩ := xs
  apply Array.ext
  · simp only [toArr, zipIdx, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Array.size_zipIdx]
  · intro i h1 h2
    simp only [toArr, zipIdx, Array.getElem_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_one_iff, List.getElem_toArray, List.getElem_singleton,
      Array.getElem_zipIdx]
    split <;> simp_all only [toArr, Array.size_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Array.size_zipIdx, Nat.add_zero, Prod.mk.injEq, true_and]
    · omega

def unzip (as : NonEmptyArray (α × β)) : NonEmptyArray α × NonEmptyArray β :=
  let (a, b) := as.toArr.unzip
  (match fromArray? a with | some a => a | none => ⟨as.head.1, #[]⟩,
   match fromArray? b with | some b => b | none => ⟨as.head.2, #[]⟩)

def flatMap (f : α → Array β) (xs : NonEmptyArray α) : Array β := xs.toArr.flatMap f
def flatMapNonEmpty (f : α → NonEmptyArray β) (xs : NonEmptyArray α) : NonEmptyArray β := flatten (xs.map f)

def leftpad (n : Nat) (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? (xs.toArr.leftpad n a) with
  | some res => res
  | none => xs

def rightpad (n : Nat) (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? (xs.toArr.rightpad n a) with
  | some res => res
  | none => xs

-- Functions returning potentially empty Array
def pop (xs : NonEmptyArray α) : Array α := xs.toArr.pop
def shrink (xs : NonEmptyArray α) (n : Nat) : Array α := xs.toArr.shrink n
def take (xs : NonEmptyArray α) (i : Nat) : Array α := xs.toArr.take i
def takeWhile (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.takeWhile p
def drop (xs : NonEmptyArray α) (i : Nat) : Array α := xs.toArr.drop i
def filter (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.filter p
def filterMap (f : α → Option β) (xs : NonEmptyArray α) : Array β := xs.toArr.filterMap f

def eraseIdx (xs : NonEmptyArray α) (i : Nat) (h : i < xs.size) : Array α :=
  if h0 : i = 0 then
    xs.tail
  else
    have : i - 1 < xs.tail.size := by simp only [size] at h; omega
    #[xs.head] ++ xs.tail.eraseIdx (i - 1) this

def eraseIdxIfInBounds (xs : NonEmptyArray α) (i : Nat) : Array α :=
  xs.toArr.eraseIdxIfInBounds i

def erase [BEq α] (xs : NonEmptyArray α) (a : α) : Array α := xs.toArr.erase a
def eraseP (xs : NonEmptyArray α) (p : α → Bool) : Array α := xs.toArr.eraseP p
def popWhile (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.popWhile p
def reduceOption (xs : NonEmptyArray (Option α)) : Array α := xs.toArr.reduceOption
def partition (p : α → Bool) (xs : NonEmptyArray α) : Array α × Array α := xs.toArr.partition p

def getEvenElems (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? xs.toArr.getEvenElems with
  | some res => res
  | none => ⟨xs.head, #[]⟩

def eraseReps [BEq α] (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? xs.toArr.eraseReps with
  | some res => res
  | none => ⟨xs.head, #[]⟩

-- Queries / Searches
def foldr {β} (f : α → β → β) (init : β) (xs : NonEmptyArray α) : β := xs.toArr.foldr f init
def any (xs : NonEmptyArray α) (p : α → Bool) : Bool := xs.toArr.any p
def all (xs : NonEmptyArray α) (p : α → Bool) : Bool := xs.toArr.all p
def contains [BEq α] (xs : NonEmptyArray α) (a : α) : Bool := xs.toArr.contains a
def elem [BEq α] (a : α) (xs : NonEmptyArray α) : Bool := xs.toArr.elem a
def countP (p : α → Bool) (xs : NonEmptyArray α) : Nat := xs.toArr.countP p
def count [BEq α] (a : α) (xs : NonEmptyArray α) : Nat := xs.toArr.count a
def sum [Add α] [Zero α] (xs : NonEmptyArray α) : α := xs.toArr.sum
def find? (p : α → Bool) (xs : NonEmptyArray α) : Option α := xs.toArr.find? p
def findSome? {β} (f : α → Option β) (xs : NonEmptyArray α) : Option β := xs.toArr.findSome? f
def findRev? (p : α → Bool) (xs : NonEmptyArray α) : Option α := xs.toArr.findRev? p
def findIdx? (p : α → Bool) (xs : NonEmptyArray α) : Option Nat := xs.toArr.findIdx? p
def findIdx (p : α → Bool) (xs : NonEmptyArray α) : Nat := xs.toArr.findIdx p
def findFinIdx? (p : α → Bool) (xs : NonEmptyArray α) : Option (Fin xs.size) :=
  xs.toArr.findFinIdx? p |>.map (fun ⟨i, h⟩ => ⟨i, by simp only [toArr, Array.size_append,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, size] at h ⊢; omega⟩)
def finIdxOf? [BEq α] (xs : NonEmptyArray α) (a : α) : Option (Fin xs.size) :=
  xs.toArr.finIdxOf? a |>.map (fun ⟨i, h⟩ => ⟨i, by simp only [toArr, Array.size_append,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, size] at h ⊢; omega⟩)
def idxOf? [BEq α] (xs : NonEmptyArray α) (a : α) : Option Nat := xs.toArr.idxOf? a
def idxOf [BEq α] (a : α) (xs : NonEmptyArray α) : Nat := xs.toArr.idxOf a
def getMax (xs : NonEmptyArray α) (lt : α → α → Bool) : α := xs.tail.foldl (fun best a => if lt best a then a else best) xs.head
def isEqv (xs ys : NonEmptyArray α) (p : α → α → Bool) : Bool := xs.toArr.isEqv ys.toArr p
def isPrefixOf [BEq α] (xs ys : NonEmptyArray α) : Bool := xs.toArr.isPrefixOf ys.toArr
def allDiff [BEq α] (xs : NonEmptyArray α) : Bool := xs.toArr.allDiff

-- Monadic operations
def forM [Monad m] (xs : NonEmptyArray α) (f : α → m PUnit) : m PUnit := xs.toArr.forM f
def forRevM [Monad m] (xs : NonEmptyArray α) (f : α → m PUnit) : m PUnit := xs.toArr.forRevM f
def foldlM [Monad m] {β} (f : β → α → m β) (init : β) (xs : NonEmptyArray α) : m β := xs.toArr.foldlM f init
def foldrM [Monad m] {β} (f : α → β → m β) (init : β) (xs : NonEmptyArray α) : m β := xs.toArr.foldrM f init
def anyM [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m Bool := xs.toArr.anyM p
def allM [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m Bool := xs.toArr.allM p
def findM? [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m (Option α) := xs.toArr.findM? p
def findSomeM? [Monad m] {β} (f : α → m (Option β)) (xs : NonEmptyArray α) : m (Option β) := xs.toArr.findSomeM? f
def findIdxM? [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m (Option Nat) := xs.toArr.findIdxM? p

/--
Maps each element of the non-empty array to `ω`, and combines them using the
provided binary operation `op`.
Because the array is non-empty, no initial `mempty` or `init` value is required.
-/
@[simp, inline]
def foldMap {α ω} (op : ω → ω → ω) (f : α → ω) (as : NonEmptyArray α) : ω :=
  as.tail.foldl (fun acc x => op acc (f x)) (f as.head)

/--
Map each element of a structure to an action, evaluate these actions from
left to right, and collect the results. For Applicative functors.
-/
@[simp, inline]
def mapA [Applicative m] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) :=
  (NonEmptyArray.mk · ·) <$> f as.head <*> NonEmpty.ArrayUtil.mapA f as.tail

/-- Evaluate each action in the structure from left to right, and collect the results. -/
@[simp, inline]
def sequence [Applicative m] (as : NonEmptyArray (m α)) : m (NonEmptyArray α) :=
  as.mapA id

instance : Append (NonEmptyArray α) := ⟨append⟩
instance : HAppend (NonEmptyArray α) (Array α) (NonEmptyArray α) := ⟨appendArray⟩
instance : HAppend (NonEmptyArray α) (List α) (NonEmptyArray α) := ⟨appendList⟩

@[simp] theorem toArr_singleton (a : α) : (singleton a).toArr = #[a] := by
  simp_all only [toArr, Array.append_eq_toArray_iff, List.cons_append, List.nil_append, List.cons.injEq, Array.toList_eq_nil_iff]
  apply And.intro
  · rfl
  · rfl
@[simp] theorem toArr_push (xs : NonEmptyArray α) (a : α) : (xs.push a).toArr = xs.toArr.push a := by
  simp_all only [toArr, Array.push_append]
  rfl
@[simp] theorem toArr_map (f : α → β) (xs : NonEmptyArray α) : (xs.map f).toArr = xs.toArr.map f := by
  simp_all only [toArr, Array.map_append, List.map_toArray, List.map_cons, List.map_nil]

@[simp] theorem toArr_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).toArr = Array.ofFn f := by
  simp only [toArr, ofFn, Fin.zero_eta]
  apply Array.ext
  · simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Array.size_ofFn]; omega
  · intro i h1 h2
    simp only [Array.getElem_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.lt_one_iff, List.getElem_toArray, List.getElem_singleton,
      Array.getElem_ofFn]
    split <;> rename_i h_i
    · subst h_i
      simp_all only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Array.size_ofFn, Fin.zero_eta]
    · congr; omega
@[simp] theorem size_append (xs ys : NonEmptyArray α) : (xs ++ ys).size = xs.size + ys.size := by
  show (append xs ys).size = xs.size + ys.size
  unfold append
  simp only [size, toArr, Array.append_singleton_assoc, Array.size_append, Array.size_push]
  omega
@[simp] theorem toArr_append (xs ys : NonEmptyArray α) : (xs ++ ys).toArr = xs.toArr ++ ys.toArr := by
  show (append xs ys).toArr = xs.toArr ++ ys.toArr
  unfold append
  show #[xs.head] ++ (xs.tail ++ ys.toArr) = (#[xs.head] ++ xs.tail) ++ ys.toArr
  rw [Array.append_assoc]
@[simp] theorem toArr_set (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i < xs.size) :
    (xs.set i a h).toArr = xs.toArr.set i a (by simp only [toArr, Array.size_append,
      List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]; exact h) := by
  unfold set; split
  · subst i; simp only [toArr, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.lt_add_one, Array.set_append_left, List.set_toArray, List.set_cons_zero]
  · have h' : i < xs.toArr.size := by simp only [toArr, Array.size_append, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add]; exact h
    rw [Array.set_append_right h' (by simp only [List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add]; omega)]
    simp only [toArr, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]

@[simp] theorem size_reverse (xs : NonEmptyArray α) : xs.reverse.size = xs.size := by
  simp only [size, reverse, toArr, Array.reverse_append, List.reverse_toArray, List.reverse_cons,
    List.reverse_nil, List.nil_append, Array.append_singleton, size_fromArray, Array.size_push,
    Array.size_reverse]
  omega

@[simp] theorem toArr_reverse (xs : NonEmptyArray α) : xs.reverse.toArr = xs.toArr.reverse := by
  simp only [toArr, reverse, Array.reverse_append, List.reverse_toArray, List.reverse_cons,
    List.reverse_nil, List.nil_append, Array.append_singleton, toArr_fromArray]



structure Mem (as : NonEmptyArray α) (a : α) : Prop where
  val : a ∈ as.toList

instance : Membership α (NonEmptyArray α) where
  mem := Mem

@[simp] theorem toArr_toList (xs : NonEmptyArray α) : xs.toArr.toList = xs.toList := by
  simp only [Array.toList_append]
  rfl

@[simp] def forInImpl [Monad m] (xs : NonEmptyArray α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  forIn xs.toArr init f

instance [Monad m] : ForIn m (NonEmptyArray α) α where
  forIn := forInImpl

theorem mem_def {a : α} {as : NonEmptyArray α} : a ∈ as ↔ a ∈ as.toArr := by
  constructor
  · intro ⟨h⟩; rw [Array.mem_def, toArr_toList]; exact h
  · intro h; rw [Array.mem_def, toArr_toList] at h; exact ⟨h⟩

theorem mem_head_or_tail {a : α} {as : NonEmptyArray α} : a ∈ as ↔ a = as.head ∨ a ∈ as.tail := by
  constructor
  · intro ⟨h⟩; exact (List.mem_cons.1 h).imp id (Array.mem_def.2)
  · intro h; exact ⟨List.mem_cons.2 (h.imp id (Array.mem_def.1))⟩

theorem mem_iff_getElem {a : α} {as : NonEmptyArray α} :
    a ∈ as ↔ ∃ (i : Nat) (h : i < as.size), as[i] = a := by
  simp only [mem_def, Array.mem_iff_getElem, size_toArr]
  simp_all only [toArr, size, toArr_getElem]

theorem mem_iff_exists_getElem {a : α} {as : NonEmptyArray α} :
    a ∈ as ↔ ∃ (i : Fin as.size), as[i] = a := by
  rw [mem_iff_getElem]
  constructor
  · rintro ⟨i, h, rfl⟩; exact ⟨⟨i, h⟩, rfl⟩
  · rintro ⟨⟨i, h⟩, rfl⟩; exact ⟨i, h, rfl⟩

def forIn'Impl [Monad m] (xs : NonEmptyArray α) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) : m β := forIn' xs.toArr init (fun a h => f a ⟨by
    rw [Array.mem_def, toArr_toList] at h
    exact h
  ⟩)

instance [Monad m] : ForIn' m (NonEmptyArray α) α inferInstance where
  forIn' := forIn'Impl

end NonEmptyArray

instance : Functor NonEmptyArray where
  map := NonEmptyArray.map

namespace NonEmptyArray


@[simp] theorem id_map (x : NonEmptyArray α) : id <$> x = x := by
  ext <;> simp only [Functor.map, map, id_eq, Array.map_id_fun]

@[simp] theorem map_id (as : NonEmptyArray α) : map id as = as := id_map as

@[simp] theorem comp_map (g : α → β) (h : β → γ) (x : NonEmptyArray α) : (h ∘ g) <$> x = h <$> g <$> x := by
  ext <;> simp only [Functor.map, map, Function.comp_apply, _root_.Array.map_map]

@[simp] theorem map_comp {α β γ : Type u} (g : α → β) (h : β → γ) (as : NonEmptyArray α) : map (h ∘ g) as = map h (map g as) := comp_map g h as

@[simp] def seq (fs : NonEmptyArray (α → β)) (xs : NonEmptyArray α) : NonEmptyArray β :=
  ⟨fs.head xs.head,
   (fs.head <$> xs.tail).append (fs.tail.mapNonEmptyArray (fun f => xs.map f))⟩

end NonEmptyArray

instance : Seq NonEmptyArray where
  seq fs x := NonEmptyArray.seq fs (x ())

instance : Applicative NonEmptyArray where
  pure := NonEmptyArray.singleton

instance : LawfulFunctor NonEmptyArray where
  id_map := NonEmptyArray.id_map
  comp_map := NonEmptyArray.comp_map
  map_const := rfl

namespace NonEmptyArray

-- Helps prove seq_pure and seq_assoc
@[simp] theorem map_tail (f : α → β) (xs : NonEmptyArray α) : (Functor.map f xs).tail = xs.tail.map f := rfl
@[simp] theorem map_head (f : α → β) (xs : NonEmptyArray α) : (Functor.map f xs).head = f xs.head := rfl

/--
Helper lemmas
-/

@[simp] theorem NonEmptyArray.toArr_flatten (xs : NonEmptyArray (NonEmptyArray α)) :
    xs.flatten.toArr = (xs.toArr.map toArr).flatten := by
  cases xs with | mk h t =>
  simp only [toArr, flatten, Array.map_append, List.map_toArray, List.map_cons, List.map_nil,
    Array.flatten_append, Array.flatten_singleton, Array.append_assoc, Array.mapNonEmptyArray_id]

@[simp] theorem NonEmptyArray.flatten_flatten_eq (xs : NonEmptyArray (NonEmptyArray (NonEmptyArray α))) :
    NonEmptyArray.flatten (NonEmptyArray.flatten xs) =
    NonEmptyArray.flatten (Functor.map NonEmptyArray.flatten xs) := by
  obtain ⟨⟨hh, ht⟩, t⟩ := xs
  simp_all only [flatten, Array.map_append, Array.map_map, Array.map_flatten, Array.flatten_append,
    mk.injEq, Array.mapNonEmptyArray_id]
  congr 2
  rw [Array.flatten_flatten]
  have : (Array.map Array.flatten (Array.map (Array.map toArr ∘ toArr) t)) = Array.map (toArr ∘ flatten) t := by
    simp only [Array.map_map, Function.comp_def]
    congr 1
    funext x
    exact (toArr_flatten x).symm
  rw [this]
  simp_all only [Array.map_map, Array.map_inj_left, Function.comp_apply, toArr, Array.map_append, List.map_toArray,
    List.map_cons, List.map_nil, Array.flatten_append, Array.flatten_singleton, Array.append_assoc, flatten,
    Array.mapNonEmptyArray, id_eq, map_head, map_tail, true_and]
  congr 1
  congr 1
  simp [Array.flatMap_def]

/-- `as.attach` returns a NonEmptyArray where each element is paired with a proof that it is in `as`. -/
@[simp] def attach (as : NonEmptyArray α) : NonEmptyArray { x // x ∈ as } :=
  ⟨⟨as.head, by simp only [mem_def, toArr, Array.mem_append, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false, true_or]⟩, as.tail.attach.map fun ⟨x, h⟩ => ⟨x, by simp only [mem_def,
      toArr, Array.mem_append, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, h,
      or_true]⟩⟩

@[simp] theorem size_attach (as : NonEmptyArray α) : as.attach.size = as.size := by
  simp only [size, attach, Array.size_map, Array.size_attach]

@[simp] theorem getElem_attach (as : NonEmptyArray α) (i : Nat) (h : i < as.attach.size) :
    as.attach[i] = ⟨as[i]'(by simpa only [size, attach, Array.size_map, Array.size_attach] using h), by
      have h' : i < as.size := by simpa only [size, attach, Array.size_map, Array.size_attach] using
        h
      rw [mem_def, ← toArr_getElem (h := h')]
      exact Array.getElem_mem ..⟩ := by
  apply Subtype.ext
  cases i with
  | zero => rfl
  | succ i =>
    cases as with | mk head tail =>
    have h' : i + 1 < tail.size + 1 := by
      simp only [size, attach, Array.size_map, Array.size_attach] at h
      omega
    -- The goal should now have concrete structure
    simp_all only [Nat.add_lt_add_iff_right, size, attach]
    simp only [getElem]
    simp_all only [Array.getInternal_eq_getElem, Array.getElem_map, Array.getElem_attach]

@[simp] theorem attach_map (as : NonEmptyArray α) (f : α → β) : as.attach.map (fun x => f x.val) = as.map f := by
  ext <;> simp

@[simp] theorem attach_map_val (as : NonEmptyArray α) : as.attach.map (fun x => x.val) = as := by
  simp_all only [map, attach, Array.map_map, Function.comp_apply, Array.map_subtype, Array.unattach_attach,
    Array.map_id_fun', id_eq]

@[simp] theorem toArr_attach (as : NonEmptyArray α) :
    as.attach.toArr = as.toArr.attach.map fun ⟨x, h⟩ => ⟨x, by simpa only [mem_def, toArr,
      Array.mem_append, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] using h⟩ := by
  apply Array.ext
  · simp only [toArr, attach, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Array.size_map, Array.size_attach, Array.attach_append,
    List.attach_toArray, List.attachWith_mem_toArray, List.attach_cons, List.attach_nil,
    List.map_nil, List.map_cons, List.map_toArray, Array.map_append, Array.map_map]
  · intro i h1 h2
    apply Subtype.ext
    simp only [toArr, attach, Array.getElem_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Array.getElem_map, Array.getElem_attach]
    split <;> simp_all only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, size_attach, size, Array.attach_append, List.attach_toArray, List.attachWith_mem_toArray,
      List.attach_cons, List.attach_nil, List.map_nil, List.map_cons, List.map_toArray, Array.map_append,
      Array.map_map, Array.size_map, Array.size_attach, List.getElem_toArray, List.getElem_singleton]

@[simp] theorem sizeOf_get [SizeOf α] (as : NonEmptyArray α) (i : Fin as.size) : sizeOf (as[i]) < sizeOf as := by
  obtain ⟨idx, h_idx⟩ := i
  cases idx with
  | zero =>
    -- 'as.get ⟨0, _⟩' is definitionally 'as.head'
    change sizeOf as.head < sizeOf as

    cases as with | mk hd tl =>
    change sizeOf hd < 1 + sizeOf hd + sizeOf tl
    omega

  | succ n =>
    have hn : n < as.tail.size := by
      simp only [size] at h_idx
      omega

    -- 'as.get ⟨n + 1, _⟩' is definitionally 'as.tail[n]' (proof irrelevance handles the exact proof match)
    change sizeOf (as.tail[n]'hn) < sizeOf as

    -- Extract the array theorem BEFORE breaking apart 'as'
    have step := Array.sizeOf_getElem as.tail n hn

    -- Now safely break apart 'as'
    cases as with | mk hd tl =>

    -- Expose the raw sizeOf math to the goal
    change sizeOf (tl[n]'hn) < 1 + sizeOf hd + sizeOf tl

    -- Clean up `step` so `omega` recognizes it!
    change sizeOf (tl[n]'hn) < sizeOf tl at step

    omega

@[simp] theorem sizeOf_getElem [SizeOf α] (as : NonEmptyArray α) (i : Nat) (h : i < as.size) :
    sizeOf (as[i]'h) < sizeOf as :=
  sizeOf_get as ⟨i, h⟩

@[simp] theorem sizeOf_lt_of_mem [SizeOf α] {as : NonEmptyArray α} {a : α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  rw [NonEmptyArray.mem_head_or_tail] at h
  rcases h with rfl | h_tail
  · -- case 1: 'a' is the head
    cases as with | mk hd tl =>
    change sizeOf hd < 1 + sizeOf hd + sizeOf tl
    omega
  · -- case 2: 'a' is in the tail
    have step := Array.sizeOf_lt_of_mem h_tail
    cases as with | mk hd tl =>
    change sizeOf a < 1 + sizeOf hd + sizeOf tl
    change sizeOf a < sizeOf tl at step
    omega

@[simp] theorem sizeOf_attach_elem [SizeOf α] (as : NonEmptyArray α) (x : { x // x ∈ as }) : sizeOf x.val < sizeOf as :=
  sizeOf_lt_of_mem x.property

@[simp] theorem sizeOf_head [SizeOf α] (as : NonEmptyArray α) : sizeOf as.head < sizeOf as := by
  cases as with
  | mk hd tl =>
      change sizeOf hd < 1 + sizeOf hd + sizeOf tl
      omega

@[simp] theorem sizeOf_tail [SizeOf α] (as : NonEmptyArray α) : sizeOf as.tail < sizeOf as := by
  cases as with
  | mk hd tl =>
      change sizeOf tl < 1 + sizeOf hd + sizeOf tl
      omega

end NonEmptyArray

instance : LawfulApplicative NonEmptyArray where
  map_pure g x := by
    simp only [Functor.map, NonEmptyArray.map, pure, NonEmptyArray.singleton, List.map_toArray,
      List.map_nil]

  pure_seq g x := by
    simp only [Seq.seq, NonEmptyArray.seq, pure, NonEmptyArray.singleton, Functor.map,
      Array.mapNonEmptyArray, NonEmptyArray.toArr, List.flatMap_toArray, Array.toList_append,
      Array.toList_map, List.cons_append, List.nil_append, List.flatMap_nil, Array.append_eq_append,
      Array.append_empty, NonEmptyArray.map]

  seq_pure f x := by
    apply NonEmptyArray.ext
    · simp only [Seq.seq, NonEmptyArray.seq, pure, NonEmptyArray.singleton, Functor.map,
      List.map_toArray, List.map_nil, Array.mapNonEmptyArray, NonEmptyArray.toArr,
      Array.append_empty, NonEmpty.ArrayUtil.flatMap_singleton_eq_map, Array.append_eq_append,
      Array.empty_append, NonEmptyArray.map]
    · obtain ⟨g, gt⟩ := f
      simp only [Seq.seq, NonEmptyArray.seq, pure, NonEmptyArray.singleton, Functor.map,
        List.map_toArray, List.map_nil, Array.mapNonEmptyArray, NonEmptyArray.toArr,
        Array.append_empty, NonEmpty.ArrayUtil.flatMap_singleton_eq_map, Array.append_eq_append,
        Array.empty_append, NonEmptyArray.map]

  seq_assoc x g f := by
    apply NonEmptyArray.ext
    · simp only [Seq.seq, NonEmptyArray.seq, Functor.map, Array.mapNonEmptyArray,
      NonEmptyArray.toArr, Array.append_eq_append, Array.map_append, Array.map_map,
      Array.append_assoc, NonEmptyArray.map, Function.comp_apply, Array.flatMap_append]
    · obtain ⟨xh, xt⟩ := x
      obtain ⟨gh, gt⟩ := g
      obtain ⟨fh, ft⟩ := f
      simp only [Seq.seq, NonEmptyArray.seq, Functor.map, Array.mapNonEmptyArray,
        NonEmptyArray.toArr, Array.append_eq_append, Array.map_append, Array.map_map,
        Array.append_assoc, NonEmptyArray.map, Function.comp_apply, Array.flatMap_append]
      cases xt with | mk l =>
      induction l generalizing gh gt fh ft
      · simp only [Function.comp_def, List.map_toArray, List.map_nil, Array.append_empty,
        NonEmpty.ArrayUtil.flatMap_singleton_eq_map, Array.map_map, Array.empty_append, Array.flatMap_map,
        Function.comp_apply, Array.flatMap_assoc, Array.flatMap_append, List.flatMap_toArray,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · rename_i a as ih
        simp only [Function.comp_def, List.map_toArray, List.append_toArray, List.cons_append,
          List.nil_append, Array.map_flatMap, List.map_cons, List.map_map, Array.flatMap_map,
          Function.comp_apply, Array.flatMap_assoc, Array.flatMap_append, List.flatMap_toArray,
          List.flatMap_cons, List.flatMap_nil, List.append_nil] at *
        simp only [← Array.append_assoc, List.append_toArray, List.cons_append, List.nil_append]

  seqLeft_eq x y := by
    simp only [SeqLeft.seqLeft, Seq.seq, NonEmptyArray.seq, Functor.map, NonEmptyArray.map,
      Function.const, Array.map_const, Array.mapNonEmptyArray, NonEmptyArray.toArr,
      Array.append_eq_append]

  seqRight_eq x y := by
    simp only [SeqRight.seqRight, Seq.seq, NonEmptyArray.seq, Functor.map, NonEmptyArray.map,
      Function.const, Array.map_const, id_eq, Array.map_id_fun, Array.mapNonEmptyArray,
      NonEmptyArray.toArr, Array.append_eq_append]


instance : Monad NonEmptyArray where
  bind xs f := NonEmptyArray.flatten (xs.map f)

instance : LawfulMonad NonEmptyArray where
  pure_bind x f := by
    apply NonEmptyArray.ext
    · rfl
    · simp only [bind, NonEmptyArray.flatten, pure, NonEmptyArray.singleton,
      Array.mapNonEmptyArray, NonEmptyArray.toArr, id_eq, List.map_toArray, List.map_nil,
      List.flatMap_toArray, Array.toList_append, List.cons_append, List.nil_append,
      List.flatMap_nil, Array.append_empty]

  bind_pure_comp f x := by
    apply NonEmptyArray.ext
    · rfl
    · obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyArray.flatten, pure, NonEmptyArray.singleton, Array.mapNonEmptyArray,
        NonEmptyArray.toArr, id_eq, Array.flatMap_map, Array.append_empty,
        NonEmpty.ArrayUtil.flatMap_singleton_eq_map, Array.empty_append, NonEmptyArray.map_tail]

  bind_map f x := by
    apply NonEmptyArray.ext
    · rfl
    · obtain ⟨fh, ft⟩ := f
      obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyArray.flatten, NonEmptyArray.map_head, NonEmptyArray.map_tail,
        Array.mapNonEmptyArray, NonEmptyArray.toArr, id_eq, Seq.seq, NonEmptyArray.seq,
        Array.append_eq_append, Array.flatMap_map]
      -- Simplify the remaining Functor.map and unify Array operations
      rfl


  bind_assoc x f g := by
    apply NonEmptyArray.ext
    · simp only [bind, NonEmptyArray.flatten, Array.mapNonEmptyArray, NonEmptyArray.toArr, id_eq,
      Array.map_append, Array.flatMap_append, Array.append_assoc]
    · obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyArray.flatten, Array.mapNonEmptyArray, NonEmptyArray.toArr, id_eq,
        Array.map_append, Array.flatMap_append, Array.append_assoc]
      cases xt with | mk l =>
      induction l generalizing f g
      · simp only [Array.flatMap_map, List.map_toArray, List.map_nil, List.flatMap_toArray,
        Array.toList_append, List.cons_append, List.nil_append, List.flatMap_nil,
        Array.append_empty]
      · rename_i a as ih
        simp_all only [Array.flatMap_map, List.map_toArray, List.flatMap_toArray,
          Array.toList_append, List.cons_append, List.nil_append, List.flatMap_map,
          List.flatMap_assoc, List.flatMap_cons, Array.toList_flatMap, implies_true, List.map_cons,
          List.map_append, List.flatMap_append, List.append_assoc]

section

-- Macro for creating non-empty list literals
syntax "#![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#![])                           => Lean.Macro.throwError "#! literal must contain at least one element"
  | `(#![ $head:term ])               => ``(NonEmptyArray.mk $head #[])
  | `(#![ $head:term, $tail:term,* ]) => ``(NonEmptyArray.mk $head #[$tail,*])

example : NonEmptyArray Nat := #![1, 2, 3]
example : NonEmptyArray String := #!["hello", "world"]
example : NonEmptyArray Nat := #![10]

#guard #![1, 2, 3].head = 1
#guard #![1, 2, 3].tail = #[2, 3]
#guard #![1, 2, 3].size = 3
#guard #![1, 2, 3][0] = 1
#guard #![1, 2, 3][1] = 2
#guard #![1, 2, 3][2] = 3

end

-- ============================================================
-- Coercions (downgraders)
-- ============================================================

/-- Automatically coerce `NonEmptyArray` (CorrectByConstruction) to its underlying `Array`. -/
@[inline]
instance : CoeOut (NonEmpty.ArrayCorrectByConstruction.NonEmptyArray α) (Array α) where
  coe xs := xs.toArr

@[inline]
instance : NonEmpty.DowngradeMap NonEmpty.ArrayCorrectByConstruction.NonEmptyArray where
  map := NonEmpty.ArrayCorrectByConstruction.NonEmptyArray.map

end NonEmpty.ArrayCorrectByConstruction
