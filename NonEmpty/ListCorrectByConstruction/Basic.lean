module
import Init.Data.List.Lemmas
-- public import NonEmpty.ListUtil
public import NonEmpty.DowngradeMap
import Aesop

@[expose] public section

-- why this is needed? for https://github.com/leanprover/lean4/issues/4964#issuecomment-4337841019
namespace NonEmpty.ListCorrectByConstruction

@[ext]
structure NonEmptyList (α : Type u) where
  head : α
  tail : List α
  deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

instance [ToString α] : ToString (NonEmptyList α) where
  toString a := "!" ++ toString ([a.head] ++ a.tail)

instance [Inhabited α] : Inhabited (NonEmptyList α) where
  default := ⟨default, []⟩

namespace NonEmptyList

@[simp] abbrev toList (xs : NonEmptyList α) : List α :=
  List.cons xs.head xs.tail

@[simp] protected def _root_.List.mapNonEmptyList (as : List α) (f : α → NonEmptyList β) : List β :=
  as.flatMap (fun a => (f a).toList)

@[simp] protected theorem _root_.List.mapNonEmptyList_id (as : List (NonEmptyList α)) :
    as.mapNonEmptyList id = (as.map toList).flatten := by
  simp only [List.mapNonEmptyList, List.flatMap_def, id_def]

@[simp] abbrev length (xs : NonEmptyList α) : Nat := 1 + xs.tail.length

-- @[inline_if_reduce] abbrev getElem (as : NonEmptyList α) (i : Nat) (h : i < as.length) : α :=
--   match i with
--   | 0 => as.head
--   | n + 1 =>
--     have : n < as.tail.length := by
--       -- h is n + 1 < length xs
--       -- length xs is 1 + xs.tail.length
--       simp only [length] at h
--       omega
--     as.tail[n]'this

-- @[always_inline] abbrev getElem? (as : NonEmptyList α) (i : Nat) : Option α :=
--   if h : i < as.length then some (as.getElem i h) else none

instance : GetElem (NonEmptyList α) Nat α (fun as i => i < as.length) where
  getElem as i h :=
    match i with
  | 0 => as.head
  | n + 1 =>
    have : n < as.tail.length := by
      -- h is n + 1 < length xs
      -- length xs is 1 + xs.tail.length
      simp only [length] at h
      omega
    as.tail[n]'this

instance : GetElem? (NonEmptyList α) Nat α (fun as i => i < as.length) where
  getElem? as i := if h : i < as.length then as[i]'h else none

-- @[simp] theorem getElem?_def (as : NonEmptyList α) (i : Nat) [Decidable (i < as.length)] :
--     as[i]? = if h : i < as.length then some as[i] else none := by
--   simp_all only [length]
--   split
--   next h => simp_all only [length, getElem?_pos]
--   next h => simp_all only [Nat.not_lt, length, getElem?_neg]

-- @[simp] theorem getElem!_def [Inhabited α] (as : NonEmptyList α) (i : Nat) :
--     as[i]! = match as[i]? with | some e => e | none => default := rfl

-- @[simp] theorem getElem!_def_if [Inhabited α] (as : NonEmptyList α) (i : Nat) [Decidable (i < as.length)] :
--     as[i]! = if h : i < as.length then as[i] else default := by
--   simp_all only [length, getElem!_def, getElem?_def]
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

instance : LawfulGetElem (NonEmptyList α) Nat α (fun as i => i < as.length) where
  -- getElem?_def := getElem?_def
  -- getElem!_def := getElem!_def

@[simp] theorem length_toList (as : NonEmptyList α) : as.toList.length = as.length := by
  simp_all only [toList, List.length_cons, length]
  simp +arith only

@[simp] theorem toList_getElem (as : NonEmptyList α) (i : Nat) (h : i < as.length) :
    as.toList[i]'(by simp only [length_toList]; exact h) = as[i] := by
  cases as with
  | mk hd tl => cases i with
    | zero => rfl
    | succ n => rfl

@[simp] theorem getElem?_eq_toList_getElem? (as : NonEmptyList α) (i : Nat) :
    as[i]? = as.toList[i]? := by
  have : as.length = as.toList.length := by simp only [length_toList]
  if h : i < as.length then
    have h' : i < as.toList.length := by omega
    simp only [getElem?_pos as i h, getElem?_pos as.toList i h']
    simp_all only [length, toList, List.length_cons, Option.some.injEq]
    exact Eq.symm (toList_getElem as i h)
  else
    have h' : ¬(i < as.toList.length) := by omega
    simp only [getElem?_neg as i h, getElem?_neg as.toList i h']

@[simp] abbrev fromList? (xs : List α) : Option (NonEmptyList α) :=
  match xs with
  | [] => none
  | x :: xs => some ⟨x, xs⟩

@[simp] abbrev fromList! [Inhabited α] (xs : List α) : NonEmptyList α :=
  match fromList? xs with
  | some xs => xs
  | none => panic! "Expected non-empty list"

@[simp] abbrev cons (a : α) (xs : NonEmptyList α) : NonEmptyList α :=
  ⟨a, [xs.head] ++ xs.tail⟩

@[simp] abbrev map (f : α → β) (xs : NonEmptyList α) : NonEmptyList β :=
  ⟨f xs.head, xs.tail.map f⟩

@[simp] def flatten (xs : NonEmptyList (NonEmptyList α)) : NonEmptyList α :=
  let ⟨h, t⟩ := xs
  ⟨h.head, h.tail ++ t.mapNonEmptyList id⟩

-- not needed ever
-- @[simp] def foldl (f : β → α → β) (init : β) (xs : NonEmptyList α) : β :=
--   xs.tail.foldl f (f init xs.head)

@[inline]
def foldlM1 [Monad m] (f : β → α → m β) (g : α → m β) (as : NonEmptyList α) : m β := do
  as.tail.foldlM f (← g as.head)

def foldrM1 [Monad m] (f : α → β → m β) (g : α → m β) (as : NonEmptyList α) : m β :=
  let rec go (x : α) (xs : List α) : m β :=
    match xs with
    | [] => g x
    | y :: ys => do f x (← go y ys)
  go as.head as.tail

@[simp, inline] def foldl1 (f : b -> a -> b) (g : a -> b) (as : NonEmptyList a) : b :=
  as.tail.foldl f (g as.head)

/--
Pure right fold for non-empty arrays.
`foldr1 f g [a, b, c]` is `f a (f b (g c))`
-/
@[inline]
def foldr1 (f : α → β → β) (g : α → β) (as : NonEmptyList α) : β :=
  Id.run <| as.foldrM1 (fun a b => pure (f a b)) (fun a => pure (g a))

@[simp] def mapM [Monad m] (f : α → m β) (as : NonEmptyList α) : m (NonEmptyList β) := do
  return ⟨← f as.head, ← as.tail.mapM f⟩

def mapM' [Monad m] (f : α → m β) (as : NonEmptyList α) :
    m { bs : NonEmptyList β // bs.length = as.length } := do
  let rec go (xs : List α) : m { bs : List β // bs.length = xs.length } :=
    match xs with
    | [] => return ⟨[], rfl⟩
    | x :: xs => do
      let x' ← f x
      let ⟨xs', h_xs'⟩ ← go xs
      return ⟨x' :: xs', by simp only [List.length_cons, h_xs']⟩
  let head' ← f as.head
  let ⟨tail', h_tail'⟩ ← go as.tail
  return ⟨⟨head', tail'⟩, by simp only [length, h_tail']⟩


@[simp] def mapFinIdxM [Monad m] (as : NonEmptyList α) (f : (i : Nat) → α → (h : i < as.length) → m β) : m (NonEmptyList β) :=
  return ⟨← f 0 as.head (by simp only [length]; omega),
          ← as.tail.mapFinIdxM (fun i a h => f (i + 1) a (by simp only [length] at h ⊢; omega))⟩

@[simp] def mapIdxM [Monad m] (f : Nat → α → m β) (as : NonEmptyList α) : m (NonEmptyList β) :=
  as.mapFinIdxM (fun i a _ => f i a)

/-- Map a function over a NonEmptyList, passing the index. -/
@[simp] def mapFinIdx (as : NonEmptyList α) (f : (i : Nat) → α → (h : i < as.length) → β) : NonEmptyList β :=
  ⟨f 0 as.head (by simp only [length]; omega),
   as.tail.mapFinIdx (fun i a h => f (i + 1) a (by simp only [length] at h ⊢; omega))⟩

/-- Map a function over a NonEmptyList, passing the index. -/
@[simp] def mapIdx (f : Nat → α → β) (as : NonEmptyList α) : NonEmptyList β :=
  ⟨f 0 as.head,
   as.tail.mapIdx (fun i => f (i + 1))⟩


--------------------------------------------------------------------------------
-- API Mapped from standard `List`
--------------------------------------------------------------------------------

def toListAppend (xs : NonEmptyList α) (l : List α) : List α := xs.toList ++ l

@[simp] def isEmpty (_xs : NonEmptyList α) : Bool := false

def back (xs : NonEmptyList α) : α := xs.tail.getLast? |>.getD xs.head
def back! [Inhabited α] (xs : NonEmptyList α) : α := xs.back
def back? (xs : NonEmptyList α) : Option α := some xs.back

@[simp] theorem toList_back (xs : NonEmptyList α) : xs.toList.getLast (by simp_all only [toList, ne_eq, reduceCtorEq,
  not_false_eq_true]) = xs.back := by
  obtain ⟨h, t⟩ := xs
  simp_all only [toList]
  grind [= back]

@[simp] theorem toList_back? (xs : NonEmptyList α) : xs.toList.getLast? = xs.back? := by
  obtain ⟨h, t⟩ := xs
  simp only [toList, back?, back, List.getLast?_cons]

@[simp] def singleton (a : α) : NonEmptyList α := ⟨a, []⟩

@[simp] theorem _root_.List.mapNonEmptyList_singleton (as : List α) (f : α → β) :
    as.mapNonEmptyList (fun a => singleton (f a)) = as.map f := by
  simp_all only [List.mapNonEmptyList, toList, singleton]
  exact Eq.symm List.map_eq_flatMap

@[simp] def ofFn {n : Nat} (f : Fin (n + 1) → α) : NonEmptyList α :=
  ⟨f ⟨0, by omega⟩, List.ofFn (fun (i : Fin n) => f ⟨i.val + 1, by omega⟩)⟩

@[simp] theorem length_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).length = n + 1 := by
  simp only [length, ofFn, Fin.zero_eta, List.length_ofFn]; omega

@[simp] theorem getElem_ofFn {n : Nat} (f : Fin (n + 1) → α) (i : Nat) (h : i < (ofFn f).length) :
    (ofFn f)[i] = f ⟨i, by simp only [length, length_ofFn] at h; exact h⟩ := by
  simp only [ofFn, GetElem.getElem]
  simp_all only [Fin.zero_eta, length, List.get_eq_getElem, List.getElem_ofFn]
  split
  next i h h_1 => simp_all only [length, List.length_ofFn, Fin.zero_eta]
  next i h n_1 h_1 => simp_all only [length, List.length_ofFn, Nat.succ_eq_add_one]

-- Modifications returning NonEmptyList
def concat (xs : NonEmptyList α) (a : α) : NonEmptyList α :=
  ⟨xs.head, xs.tail.concat a⟩

def set (xs : NonEmptyList α) (i : Nat) (a : α) (h : i < xs.length) : NonEmptyList α :=
  if h0 : i = 0 then
    ⟨a, xs.tail⟩
  else
    have : i - 1 < xs.tail.length := by simp only [length] at h; omega
    ⟨xs.head, xs.tail.set (i - 1) a⟩

def set! (xs : NonEmptyList α) (i : Nat) (a : α) : NonEmptyList α :=
  if h : i < xs.length then xs.set i a h else
    have : Inhabited (NonEmptyList α) := ⟨xs⟩
    panic! "invalid index"

def modify (xs : NonEmptyList α) (i : Nat) (f : α → α) : NonEmptyList α :=
  if h : i < xs.length then
    if h0 : i = 0 then ⟨f xs.head, xs.tail⟩
    else
      have : i - 1 < xs.tail.length := by simp only [length] at h; omega
      ⟨xs.head, xs.tail.modify (i - 1) f⟩
  else xs

-- commented out bc List dont have modifyM (weirdly)
-- def modifyM [Monad m] (xs : NonEmptyList α) (i : Nat) (f : α → m α) : m (NonEmptyList α) := do
--   if h : i < xs.length then
--     if h0 : i = 0 then return ⟨← f xs.head, xs.tail⟩
--     else
--       have : i - 1 < xs.tail.length := by simp only [length] at h; omega
--       return ⟨xs.head, ← xs.tail.modifyM (i - 1) f⟩
--   else return xs

-- def swap (xs : NonEmptyList α) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) : NonEmptyList α :=
--   if h0 : i = 0 ∧ j = 0 then xs
--   else if h1 : i = 0 then
--     let j' := j - 1; have : j' < xs.tail.length := by simp only [length] at hj; omega
--     ⟨xs.tail[j'], xs.tail.set j' xs.head this⟩
--   else if h2 : j = 0 then
--     let i' := i - 1; have : i' < xs.tail.length := by simp only [length] at hi; omega
--     ⟨xs.tail[i'], xs.tail.set i' xs.head this⟩
--   else
--     let i' := i - 1; have hi' : i' < xs.tail.length := by simp only [length] at hi; omega
--     let j' := j - 1; have hj' : j' < xs.tail.length := by simp only [length] at hj; omega
--     ⟨xs.head, xs.tail.swap i' j' hi' hj'⟩

-- def swap! (xs : NonEmptyList α) (i j : Nat) : NonEmptyList α :=
--   if hi : i < xs.length then
--     if hj : j < xs.length then xs.swap i j hi hj
--     else
--       have : Inhabited (NonEmptyList α) := ⟨xs⟩
--       panic! "invalid index"
--   else
--     have : Inhabited (NonEmptyList α) := ⟨xs⟩
--     panic! "invalid index"

-- def swapAt (xs : NonEmptyList α) (i : Nat) (v : α) (hi : i < xs.length) : α × NonEmptyList α :=
--   (xs[i]'hi, xs.set i v hi)

-- def swapAt! (xs : NonEmptyList α) (i : Nat) (v : α) : α × NonEmptyList α :=
--   if hi : i < xs.length then xs.swapAt i v hi
--   else
--     have : Inhabited (α × NonEmptyList α) := ⟨(v, xs)⟩
--     panic! "invalid index"

def fromList (xs : List α) (h : xs.length > 0) : NonEmptyList α :=
  ⟨xs[0]'h, xs.extract 1 xs.length⟩


@[simp] theorem toList_fromList (xs : List α) (h : xs.length > 0) :
  (fromList xs h).toList = xs := by
  simp only [toList, fromList]
  cases xs with
  | nil => contradiction
  | cons x xs' =>
    simp only [List.extract_eq_take_drop, List.drop_succ_cons, List.drop_zero, List.length_cons,
      Nat.add_sub_cancel, List.take_length, List.getElem_cons_zero]

@[simp] theorem length_fromList (xs : List α) (h : xs.length > 0) :
  (fromList xs h).length = xs.length := by
  simp_all only [length]
  grind [= tail.eq_def, = fromList.eq_def]

@[simp] theorem getElem_fromList (xs : List α) (h : xs.length > 0) (i : Nat) (hi : i < (fromList xs h).length) :
  (fromList xs h)[i] = xs[i]'(by simpa only [length, length_fromList] using hi) := by
  cases i with
  | zero => rfl
  | succ i =>
    cases xs with
    | nil => contradiction
    | cons x xs' =>
      have eq1 : (x :: xs').length - 1 = xs'.length := rfl
      simp only [fromList, GetElem.getElem]
      simp_all only [List.length_cons, Nat.add_one_sub_one, List.get_eq_getElem,
        List.getElem_cons_succ]
      simp only [List.extract_eq_take_drop, Nat.add_one_sub_one, List.drop_succ_cons,
        List.drop_zero, List.take_length]

def reverse (xs : NonEmptyList α) : NonEmptyList α :=
  let arr := xs.toList.reverse
  have : arr.length > 0 := by
    simp_all only [List.reverse_cons, List.length_append, List.length_reverse, List.length_cons, List.length_nil,
      Nat.zero_add, gt_iff_lt, Nat.zero_lt_succ, arr]
  fromList arr this

def append (xs ys : NonEmptyList α) : NonEmptyList α :=
  ⟨xs.head, xs.tail ++ ys.toList⟩

def appendList (xs : NonEmptyList α) (ys : List α) : NonEmptyList α :=
  ⟨xs.head, xs.tail ++ ys⟩

def insertIdx (xs : NonEmptyList α) (i : Nat) (a : α) (h : i ≤ xs.length) : NonEmptyList α :=
  if h0 : i = 0 then
    ⟨a, xs.toList⟩
  else
    have : i - 1 ≤ xs.tail.length := by simp only [length] at h; omega
    ⟨xs.head, xs.tail.insertIdx (i - 1) a⟩

def insertIdxIfInBounds (xs : NonEmptyList α) (i : Nat) (a : α) : NonEmptyList α :=
  if h : i ≤ xs.length then xs.insertIdx i a h else xs

def replace [BEq α] (xs : NonEmptyList α) (a b : α) : NonEmptyList α :=
  if xs.head == a then ⟨b, xs.tail⟩
  else ⟨xs.head, xs.tail.replace a b⟩

def zipWith (f : α → β → γ) (as : NonEmptyList α) (bs : NonEmptyList β) : NonEmptyList γ :=
  ⟨f as.head bs.head, as.tail.zipWith f bs.tail⟩

def zipWithAll (f : Option α → Option β → γ) (as : NonEmptyList α) (bs : NonEmptyList β) : NonEmptyList γ :=
  match fromList? (as.toList.zipWithAll f bs.toList) with
  | some res => res
  | none => ⟨f (some as.head) (some bs.head), []⟩

def zipWithM [Monad m] (f : α → β → m γ) (as : NonEmptyList α) (bs : NonEmptyList β) : m (NonEmptyList γ) := do
  return ⟨← f as.head bs.head, ← as.tail.zipWithM f bs.tail⟩

def zip (as : NonEmptyList α) (bs : NonEmptyList β) : NonEmptyList (α × β) :=
  as.zipWith Prod.mk bs

def zipIdx (xs : NonEmptyList α) (start := 0) : NonEmptyList (α × Nat) :=
  ⟨(xs.head, start), xs.tail.zipIdx (start + 1)⟩

@[simp] theorem toList_zipIdx (xs : NonEmptyList α) (start := 0) :
    (xs.zipIdx start).toList = xs.toList.zipIdx start := by
  obtain ⟨head, tail⟩ := xs
  simp_all only [toList, List.zipIdx_cons, List.cons.injEq]
  apply And.intro
  · rfl
  · rfl

def unzip (as : NonEmptyList (α × β)) : NonEmptyList α × NonEmptyList β :=
  let (a, b) := as.toList.unzip
  (match fromList? a with | some a => a | none => ⟨as.head.1, []⟩,
   match fromList? b with | some b => b | none => ⟨as.head.2, []⟩)

def flatMap (f : α → List β) (xs : NonEmptyList α) : List β := xs.toList.flatMap f
def flatMapNonEmpty (f : α → NonEmptyList β) (xs : NonEmptyList α) : NonEmptyList β := flatten (xs.map f)

def leftpad (n : Nat) (a : α) (xs : NonEmptyList α) : NonEmptyList α :=
  match fromList? (xs.toList.leftpad n a) with
  | some res => res
  | none => xs

def rightpad (n : Nat) (a : α) (xs : NonEmptyList α) : NonEmptyList α :=
  match fromList? (xs.toList.rightpad n a) with
  | some res => res
  | none => xs

-- Functions returning potentially empty List
-- def pop (xs : NonEmptyList α) : List α := xs.toList.pop
-- def shrink (xs : NonEmptyList α) (n : Nat) : List α := xs.toList.shrink n
def take (xs : NonEmptyList α) (i : Nat) : List α := xs.toList.take i
def takeWhile (p : α → Bool) (xs : NonEmptyList α) : List α := xs.toList.takeWhile p
def drop (xs : NonEmptyList α) (i : Nat) : List α := xs.toList.drop i
def filter (p : α → Bool) (xs : NonEmptyList α) : List α := xs.toList.filter p
def filterMap (f : α → Option β) (xs : NonEmptyList α) : List β := xs.toList.filterMap f

def eraseIdx (xs : NonEmptyList α) (i : Nat) : List α :=
  if i = 0 then
    xs.tail
  else
    xs.head :: xs.tail.eraseIdx (i - 1)

-- def eraseIdxIfInBounds (xs : NonEmptyList α) (i : Nat) : List α :=
--   xs.toList.eraseIdxIfInBounds i

def erase [BEq α] (xs : NonEmptyList α) (a : α) : List α := xs.toList.erase a
def eraseP (xs : NonEmptyList α) (p : α → Bool) : List α := xs.toList.eraseP p
-- def popWhile (p : α → Bool) (xs : NonEmptyList α) : List α := xs.toList.popWhile p
def reduceOption (xs : NonEmptyList (Option α)) : List α := xs.toList.reduceOption
def partition (p : α → Bool) (xs : NonEmptyList α) : List α × List α := xs.toList.partition p

-- def getEvenElems (xs : NonEmptyList α) : NonEmptyList α :=
--   match fromList? xs.toList.getEvenElems with
--   | some res => res
--   | none => ⟨xs.head, []⟩

def eraseReps [BEq α] (xs : NonEmptyList α) : NonEmptyList α :=
  match fromList? xs.toList.eraseReps with
  | some res => res
  | none => ⟨xs.head, []⟩

-- Queries / Searches
def foldr {β} (f : α → β → β) (init : β) (xs : NonEmptyList α) : β := xs.toList.foldr f init
def any (xs : NonEmptyList α) (p : α → Bool) : Bool := xs.toList.any p
def all (xs : NonEmptyList α) (p : α → Bool) : Bool := xs.toList.all p
def contains [BEq α] (xs : NonEmptyList α) (a : α) : Bool := xs.toList.contains a
def elem [BEq α] (a : α) (xs : NonEmptyList α) : Bool := xs.toList.elem a
def countP (p : α → Bool) (xs : NonEmptyList α) : Nat := xs.toList.countP p
def count [BEq α] (a : α) (xs : NonEmptyList α) : Nat := xs.toList.count a
def sum [Add α] [Zero α] (xs : NonEmptyList α) : α := xs.toList.sum
def find? (p : α → Bool) (xs : NonEmptyList α) : Option α := xs.toList.find? p
def findSome? {β} (f : α → Option β) (xs : NonEmptyList α) : Option β := xs.toList.findSome? f
def findRev? (p : α → Bool) (xs : NonEmptyList α) : Option α := xs.toList.findRev? p
def findIdx? (p : α → Bool) (xs : NonEmptyList α) : Option Nat := xs.toList.findIdx? p
def findIdx (p : α → Bool) (xs : NonEmptyList α) : Nat := xs.toList.findIdx p
def findFinIdx? (p : α → Bool) (xs : NonEmptyList α) : Option (Fin xs.length) :=
  xs.toList.findFinIdx? p |>.map (fun ⟨i, h⟩ => ⟨i, by
  simp only [toList, List.length_cons, length] at h ⊢; omega⟩)
def finIdxOf? [BEq α] (xs : NonEmptyList α) (a : α) : Option (Fin xs.length) :=
  xs.toList.finIdxOf? a |>.map (fun ⟨i, h⟩ => ⟨i, by simp only [toList, List.length_cons, length] at h ⊢; omega⟩)
def idxOf? [BEq α] (xs : NonEmptyList α) (a : α) : Option Nat := xs.toList.idxOf? a
def idxOf [BEq α] (a : α) (xs : NonEmptyList α) : Nat := xs.toList.idxOf a
def getMax (xs : NonEmptyList α) (lt : α → α → Bool) : α := xs.tail.foldl (fun best a => if lt best a then a else best) xs.head
def isEqv (xs ys : NonEmptyList α) (p : α → α → Bool) : Bool := xs.toList.isEqv ys.toList p
def isPrefixOf [BEq α] (xs ys : NonEmptyList α) : Bool := xs.toList.isPrefixOf ys.toList
-- def allDiff [BEq α] (xs : NonEmptyList α) : Bool := xs.toList.allDiff

-- Monadic operations
def forM [Monad m] (xs : NonEmptyList α) (f : α → m PUnit) : m PUnit := xs.toList.forM f
-- def forRevM [Monad m] (xs : NonEmptyList α) (f : α → m PUnit) : m PUnit := xs.toList.forRevM f
def foldlM [Monad m] {β} (f : β → α → m β) (init : β) (xs : NonEmptyList α) : m β := xs.toList.foldlM f init
def foldrM [Monad m] {β} (f : α → β → m β) (init : β) (xs : NonEmptyList α) : m β := xs.toList.foldrM f init
def anyM [Monad m] (p : α → m Bool) (xs : NonEmptyList α) : m Bool := xs.toList.anyM p
def allM [Monad m] (p : α → m Bool) (xs : NonEmptyList α) : m Bool := xs.toList.allM p
def findM? [Monad m] (p : α → m Bool) (xs : NonEmptyList α) : m (Option α) := xs.toList.findM? p
def findSomeM? [Monad m] {β} (f : α → m (Option β)) (xs : NonEmptyList α) : m (Option β) := xs.toList.findSomeM? f
def findIdxM? [Monad m] (p : α → m Bool) (xs : NonEmptyList α) : m (Option Nat) :=
  let rec go (i : Nat) (ys : List α) : m (Option Nat) :=
    match ys with
    | [] => return none
    | y :: ys' => do
      if ← p y then return some i else go (i + 1) ys'
  go 0 xs.toList

/--
Maps each element of the non-empty array to `ω`, and combines them using the
provided binary operation `op`.
Because the array is non-empty, no initial `mempty` or `init` value is required.
-/
@[simp, inline]
def foldMap {α ω} (op : ω → ω → ω) (f : α → ω) (as : NonEmptyList α) : ω :=
  as.tail.foldl (fun acc x => op acc (f x)) (f as.head)

/--
Map each element of a structure to an action, evaluate these actions from
left to right, and collect the results. For Applicative functors.
-/
@[simp, inline]
def mapA [Applicative m] (f : α → m β) (as : NonEmptyList α) : m (NonEmptyList β) :=
  (NonEmptyList.mk · ·) <$> f as.head <*> as.tail.mapA f

/-- Evaluate each action in the structure from left to right, and collect the results. -/
@[simp, inline]
def sequence [Applicative m] (as : NonEmptyList (m α)) : m (NonEmptyList α) :=
  as.mapA id

instance : Append (NonEmptyList α) := ⟨append⟩
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) := ⟨appendList⟩
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) := ⟨appendList⟩

@[simp] theorem toList_singleton (a : α) : (singleton a).toList = [a] := by
  simp_all only [toList, singleton]
@[simp] theorem toList_concat (xs : NonEmptyList α) (a : α) : (xs.concat a).toList = xs.toList.concat a := by
  simp_all only [toList, List.concat_eq_append, List.cons_append, List.cons.injEq]
  apply And.intro
  · rfl
  · grind only [concat, = List.concat_eq_append]
@[simp] theorem toList_map (f : α → β) (xs : NonEmptyList α) : (xs.map f).toList = xs.toList.map f := by
  simp_all only [toList, List.map_cons]

@[simp] theorem toList_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).toList = List.ofFn f := by
  simp only [toList, ofFn, Fin.zero_eta]
  simp_all only [List.ofFn_succ, List.cons.injEq, true_and]
  rfl
@[simp] theorem length_append (xs ys : NonEmptyList α) : (xs ++ ys).length = xs.length + ys.length := by
  show (append xs ys).length = xs.length + ys.length
  unfold append
  simp_all only [length, toList, List.length_append, List.length_cons]
  simp +arith only
@[simp] theorem toList_append (xs ys : NonEmptyList α) : (xs ++ ys).toList = xs.toList ++ ys.toList := by
  show (append xs ys).toList = xs.toList ++ ys.toList
  unfold append
  show [xs.head] ++ (xs.tail ++ ys.toList) = ([xs.head] ++ xs.tail) ++ ys.toList
  rw [List.append_assoc]
@[simp] theorem toList_set (xs : NonEmptyList α) (i : Nat) (a : α) (h : i < xs.length) :
    (xs.set i a h).toList = xs.toList.set i a := by
  unfold set; split
  · rename_i h_1
    subst h_1
    simp_all only [length, toList, List.set_cons_zero]
  · cases i with
    | zero => contradiction
    | succ i' => rfl

@[simp] theorem length_reverse (xs : NonEmptyList α) : xs.reverse.length = xs.length := by
  simp only [reverse, length_fromList, List.length_reverse, length_toList]

@[simp] theorem toList_reverse (xs : NonEmptyList α) : xs.reverse.toList = xs.toList.reverse := by
  simp only [reverse, toList_fromList]

structure Mem (as : NonEmptyList α) (a : α) : Prop where
  val : a ∈ as.toList

instance : Membership α (NonEmptyList α) where
  mem := Mem

def toArray (xs : NonEmptyList α) : Array α := xs.toList.toArray

@[simp] theorem toList_toArray (xs : NonEmptyList α) : xs.toArray.toList = xs.toList := by
  simp [toArray]

@[simp] def forInImpl [Monad m] (xs : NonEmptyList α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  forIn xs.toList init f

instance [Monad m] : ForIn m (NonEmptyList α) α where
  forIn := forInImpl

theorem mem_def {a : α} {as : NonEmptyList α} : a ∈ as ↔ a ∈ as.toList := by
  constructor
  · intro ⟨h⟩; exact h
  · intro h; exact ⟨h⟩

theorem mem_head_or_tail {a : α} {as : NonEmptyList α} : a ∈ as ↔ a = as.head ∨ a ∈ as.tail := by
  constructor
  · intro ⟨h⟩; exact List.mem_cons.1 h
  · intro h; exact ⟨List.mem_cons.2 h⟩

theorem mem_iff_getElem {a : α} {as : NonEmptyList α} :
    a ∈ as ↔ ∃ (i : Nat) (h : i < as.length), as[i] = a := by
  simp only [mem_def, List.mem_iff_getElem, length_toList]
  simp_all only [toList, length, toList_getElem]

theorem mem_iff_exists_getElem {a : α} {as : NonEmptyList α} :
    a ∈ as ↔ ∃ (i : Fin as.length), as[i] = a := by
  rw [mem_iff_getElem]
  constructor
  · rintro ⟨i, h, rfl⟩; exact ⟨⟨i, h⟩, rfl⟩
  · rintro ⟨⟨i, h⟩, rfl⟩; exact ⟨i, h, rfl⟩

def forIn'Impl [Monad m] (xs : NonEmptyList α) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) : m β := forIn' xs.toList init (fun a h => f a ⟨h⟩)

instance [Monad m] : ForIn' m (NonEmptyList α) α inferInstance where
  forIn' := forIn'Impl

end NonEmptyList

instance : Functor NonEmptyList where
  map := NonEmptyList.map

namespace NonEmptyList


@[simp] theorem id_map (x : NonEmptyList α) : id <$> x = x := by
  ext <;> simp only [Functor.map, map, id_eq, List.map_id_fun]

@[simp] theorem map_id (as : NonEmptyList α) : map id as = as := id_map as

@[simp] theorem comp_map (g : α → β) (h : β → γ) (x : NonEmptyList α) : (h ∘ g) <$> x = h <$> g <$> x := by
  ext <;> simp only [Functor.map, map, Function.comp_apply, _root_.List.map_map]

@[simp] theorem map_comp {α β γ : Type u} (g : α → β) (h : β → γ) (as : NonEmptyList α) : map (h ∘ g) as = map h (map g as) := comp_map g h as

@[simp] def seq (fs : NonEmptyList (α → β)) (xs : NonEmptyList α) : NonEmptyList β :=
  ⟨fs.head xs.head,
   (fs.head <$> xs.tail).append (fs.tail.mapNonEmptyList (fun f => xs.map f))⟩

end NonEmptyList

instance : Seq NonEmptyList where
  seq fs x := NonEmptyList.seq fs (x ())

instance : Applicative NonEmptyList where
  pure := NonEmptyList.singleton

instance : LawfulFunctor NonEmptyList where
  id_map := NonEmptyList.id_map
  comp_map := NonEmptyList.comp_map
  map_const := rfl

namespace NonEmptyList

-- Helps prove seq_pure and seq_assoc
@[simp] theorem map_tail (f : α → β) (xs : NonEmptyList α) : (Functor.map f xs).tail = xs.tail.map f := rfl
@[simp] theorem map_head (f : α → β) (xs : NonEmptyList α) : (Functor.map f xs).head = f xs.head := rfl

/--
Helper lemmas
-/

@[simp] theorem NonEmptyList.toList_flatten (xs : NonEmptyList (NonEmptyList α)) :
    xs.flatten.toList = (xs.toList.map toList).flatten := by
  simp_all only [toList, flatten, List.mapNonEmptyList, id_eq, List.map_cons, List.flatten_cons, List.cons_append,
    List.cons.injEq, List.append_cancel_left_eq, true_and]
  rfl

@[simp] theorem NonEmptyList.flatten_flatten_eq (xs : NonEmptyList (NonEmptyList (NonEmptyList α))) :
    NonEmptyList.flatten (NonEmptyList.flatten xs) =
    NonEmptyList.flatten (Functor.map NonEmptyList.flatten xs) := by
  obtain ⟨⟨hh, ht⟩, t⟩ := xs
  simp_all only [flatten, List.map_append, List.map_map, List.map_flatten, List.flatten_append,
    mk.injEq, List.mapNonEmptyList_id]
  congr 2
  rw [List.flatten_flatten]
  have : (List.map List.flatten (List.map (List.map toList ∘ toList) t)) = List.map (toList ∘ flatten) t := by
    simp only [List.map_map, Function.comp_def]
    congr 1
  rw [this]
  simp_all only [List.map_map, List.map_inj_left, Function.comp_apply, toList, List.map_cons, List.flatten_cons,
    List.cons_append, flatten, List.mapNonEmptyList, id_eq, List.cons.injEq, List.append_cancel_left_eq, true_and,
    map_head, map_tail, List.append_assoc, List.append_cancel_right_eq]
  rfl

/-- `as.attach` returns a NonEmptyList where each element is paired with a proof that it is in `as`. -/
@[simp] def attach (as : NonEmptyList α) : NonEmptyList { x // x ∈ as } :=
  ⟨⟨as.head, by
    solve_by_elim
  ⟩, as.tail.attach.map fun ⟨x, h⟩ => ⟨x, by
    solve_by_elim
  ⟩⟩

@[simp] theorem length_attach (as : NonEmptyList α) : as.attach.length = as.length := by
  simp only [length, attach, List.length_map, List.length_attach]

@[simp] theorem getElem_attach (as : NonEmptyList α) (i : Nat) (h : i < as.attach.length) :
    as.attach[i] = ⟨as[i]'(by simpa only [length, attach, List.length_map, List.length_attach] using h), by
      have h' : i < as.length := by simpa only [length, attach, List.length_map, List.length_attach] using
        h
      rw [mem_def, ← toList_getElem (h := h')]
      exact List.getElem_mem ..⟩ := by
  apply Subtype.ext
  cases i with
  | zero => rfl
  | succ i =>
    cases as with | mk head tail =>
    have h' : i + 1 < tail.length + 1 := by
      simp only [length, attach, List.length_map, List.length_attach] at h
      omega
    -- The goal should now have concrete structure
    simp_all only [Nat.add_lt_add_iff_right, length, attach]
    simp only [getElem]
    simp_all only [List.get_eq_getElem, List.getElem_map, List.getElem_attach]

@[simp] theorem attach_map (as : NonEmptyList α) (f : α → β) : as.attach.map (fun x => f x.val) = as.map f := by
  ext <;> simp

@[simp] theorem attach_map_val (as : NonEmptyList α) : as.attach.map (fun x => x.val) = as := by
  simp_all only [map, attach, List.map_map, Function.comp_apply, List.map_subtype, List.unattach_attach,
    List.map_id_fun', id_eq]

@[simp] theorem toList_attach (as : NonEmptyList α) :
    as.attach.toList = as.toList.attach.map fun ⟨x, h⟩ => ⟨x, by
    solve_by_elim
  ⟩ := by
  simp_all only [toList, attach, List.attach_cons, List.map_cons, List.map_map, List.cons.injEq, List.map_inj_left,
    List.mem_attach, Function.comp_apply, imp_self, implies_true, and_self]

@[simp] theorem sizeOf_get [SizeOf α] (as : NonEmptyList α) (i : Fin as.length) : sizeOf (as[i]) < sizeOf as := by
  obtain ⟨idx, h_idx⟩ := i
  cases idx with
  | zero =>
    -- 'as.get ⟨0, _⟩' is definitionally 'as.head'
    change sizeOf as.head < sizeOf as

    cases as with | mk hd tl =>
    change sizeOf hd < 1 + sizeOf hd + sizeOf tl
    omega

  | succ n =>
    have hn : n < as.tail.length := by
      simp_all only [length]
      grind only

    -- 'as.get ⟨n + 1, _⟩' is definitionally 'as.tail[n]' (proof irrelevance handles the exact proof match)
    change sizeOf (as.tail[n]'hn) < sizeOf as

    -- Extract the array theorem BEFORE breaking apart 'as'
    have step := List.sizeOf_get as.tail ⟨n, hn⟩

    -- Now safely break apart 'as'
    cases as with | mk hd tl =>

    -- Expose the raw sizeOf math to the goal
    change sizeOf (tl[n]'hn) < 1 + sizeOf hd + sizeOf tl

    -- Clean up `step` so `omega` recognizes it!
    change sizeOf (tl[n]'hn) < sizeOf tl at step

    omega

@[simp] theorem sizeOf_getElem [SizeOf α] (as : NonEmptyList α) (i : Nat) (h : i < as.length) :
    sizeOf (as[i]'h) < sizeOf as :=
  sizeOf_get as ⟨i, h⟩

@[simp] theorem sizeOf_lt_of_mem [SizeOf α] {as : NonEmptyList α} {a : α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  rw [NonEmptyList.mem_head_or_tail] at h
  rcases h with rfl | h_tail
  · -- case 1: 'a' is the head
    cases as with | mk hd tl =>
    change sizeOf hd < 1 + sizeOf hd + sizeOf tl
    omega
  · -- case 2: 'a' is in the tail
    have step := List.sizeOf_lt_of_mem h_tail
    cases as with | mk hd tl =>
    change sizeOf a < 1 + sizeOf hd + sizeOf tl
    change sizeOf a < sizeOf tl at step
    omega

@[simp] theorem sizeOf_attach_elem [SizeOf α] (as : NonEmptyList α) (x : { x // x ∈ as }) : sizeOf x.val < sizeOf as :=
  sizeOf_lt_of_mem x.property

@[simp] theorem sizeOf_head [SizeOf α] (as : NonEmptyList α) : sizeOf as.head < sizeOf as := by
  cases as with
  | mk hd tl =>
      change sizeOf hd < 1 + sizeOf hd + sizeOf tl
      omega

@[simp] theorem sizeOf_tail [SizeOf α] (as : NonEmptyList α) : sizeOf as.tail < sizeOf as := by
  cases as with
  | mk hd tl =>
      change sizeOf tl < 1 + sizeOf hd + sizeOf tl
      omega

end NonEmptyList

private theorem flatMap_flatMap_aux {α β γ} (l : List α) (h1 : α → List β) (h2 : β → List γ) :
    (l.flatMap h1).flatMap h2 = l.flatMap (fun a => (h1 a).flatMap h2) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih]

instance : LawfulApplicative NonEmptyList where
  map_pure g x := by
    rfl

  pure_seq g x := by
    cases x; simp [Seq.seq, NonEmptyList.seq, pure, NonEmptyList.singleton, Functor.map, NonEmptyList.map, List.mapNonEmptyList]

  seq_pure f x := by
    apply NonEmptyList.ext
    · rfl
    · obtain ⟨fh, ft⟩ := f
      simp only [Seq.seq, NonEmptyList.seq, pure, NonEmptyList.singleton, Functor.map, NonEmptyList.map, List.map_nil]
      exact List.mapNonEmptyList_singleton ft (fun h => h x)

  seq_assoc x g f := by
    apply NonEmptyList.ext
    · rfl
    · obtain ⟨xh, xt⟩ := x
      obtain ⟨gh, gt⟩ := g
      obtain ⟨fh, ft⟩ := f
      simp only [Seq.seq, NonEmptyList.seq, Functor.map, NonEmptyList.map, List.mapNonEmptyList,
        NonEmptyList.toList, List.append_eq]
      simp_all only [List.map_append, List.flatMap_append, List.append_assoc, List.flatMap_map, List.map_flatMap, List.map_map, List.flatMap_cons, List.map_cons, Function.comp_apply, flatMap_flatMap_aux, List.cons_append]

  seqLeft_eq x y := by
    simp only [SeqLeft.seqLeft, Seq.seq, NonEmptyList.seq, Functor.map, NonEmptyList.map,
      Function.const, List.map_const, List.mapNonEmptyList, NonEmptyList.toList]

  seqRight_eq x y := by
    simp only [SeqRight.seqRight, Seq.seq, NonEmptyList.seq, Functor.map, NonEmptyList.map,
      Function.const, List.map_const, id_eq, List.map_id_fun, List.mapNonEmptyList,
      NonEmptyList.toList]


instance : Monad NonEmptyList where
  bind xs f := NonEmptyList.flatten (xs.map f)

instance : LawfulMonad NonEmptyList where
  pure_bind x f := by
    apply NonEmptyList.ext
    · rfl
    · simp only [bind, NonEmptyList.flatten, pure, NonEmptyList.singleton,
        List.mapNonEmptyList, NonEmptyList.toList, id_eq, List.map_nil,
        List.flatMap_nil, List.append_nil]

  bind_pure_comp f x := by
    apply NonEmptyList.ext
    · rfl
    · simp_all only [NonEmptyList.map_tail]
      simp only [bind, pure, NonEmptyList.singleton, NonEmptyList.flatten, List.mapNonEmptyList,
        NonEmptyList.toList, id_eq, List.map_eq_flatMap, flatMap_flatMap_aux, List.nil_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

  bind_map f x := by
    apply NonEmptyList.ext
    · rfl
    · obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyList.flatten, List.mapNonEmptyList, NonEmptyList.toList, id_eq,
        Seq.seq, NonEmptyList.seq, List.flatMap_map, Functor.map, NonEmptyList.map]
      rfl

  bind_assoc x f g := by
    apply NonEmptyList.ext
    · simp only [bind, NonEmptyList.flatten, List.mapNonEmptyList, NonEmptyList.toList, id_eq,
      List.map_append, List.flatMap_append, List.append_assoc]
    · obtain ⟨xh, xt⟩ := x
      simp only [bind, NonEmptyList.flatten, List.mapNonEmptyList, NonEmptyList.toList, id_eq,
        List.map_append, List.flatMap_append, List.append_assoc]
      simp_all only [List.append_cancel_left_eq]
      simp only [List.map_eq_flatMap, flatMap_flatMap_aux]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append]
section

-- Macro for creating non-empty list literals
syntax "![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(![])                           => Lean.Macro.throwError "! literal must contain at least one element"
  | `(![ $head:term ])               => ``(NonEmptyList.mk $head [])
  | `(![ $head:term, $tail:term,* ]) => ``(NonEmptyList.mk $head [$tail,*])

example : NonEmptyList Nat := ![1, 2, 3]
example : NonEmptyList String := !["hello", "world"]
example : NonEmptyList Nat := ![10]

#guard ![1, 2, 3].head = 1
#guard ![1, 2, 3].tail = [2, 3]
#guard ![1, 2, 3].length = 3
#guard ![1, 2, 3][0] = 1
#guard ![1, 2, 3][1] = 2
#guard ![1, 2, 3][2] = 3

end

-- ============================================================
-- Coercions (downgraders)
-- ============================================================

/-- Automatically coerce `NonEmptyList` (CorrectByConstruction) to its underlying `List`. -/
@[inline]
instance : CoeOut (NonEmpty.ListCorrectByConstruction.NonEmptyList α) (List α) where
  coe xs := xs.toList

@[inline]
instance : NonEmpty.DowngradeMap NonEmpty.ListCorrectByConstruction.NonEmptyList where
  map := NonEmpty.ListCorrectByConstruction.NonEmptyList.map

end NonEmpty.ListCorrectByConstruction
