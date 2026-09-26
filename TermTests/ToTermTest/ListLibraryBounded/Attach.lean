module

public import TermTests.ToTermTest.ListLibraryBounded.Common
public meta import LeanScript.KernelRfl

@[expose] public section

/-! # `List.range` and `List.attach`, on every small input

The programs `rangeOnly`, `rangeDouble`, `attachVal`, `rangeIndex` and `attachWithSum` of `TermTests/ToTermTest/ListLibrary.lean`, translated, agree with the Lean functions on every natural number below `12` and every list of length at most `3` with entries below `4`.  See `TermTests/ToTermTest/ListLibraryBounded/Common.lean`. -/

namespace TermTests.ToTerm.ListLibrary

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split

set_option maxRecDepth 20000

theorem rangeOnly_term_small (n : Nat) (hn : n < 12) :
    readNatList (runAdd rangeOnly_term n) = rangeOnly n :=
  (by decide +kernel : ∀ n < 12, readNatList (runAdd rangeOnly_term n) = rangeOnly n) n hn

theorem rangeDouble_term_small (n : Nat) (hn : n < 12) :
    readNatList (runAdd rangeDouble_term n) = rangeDouble n :=
  (by decide +kernel : ∀ n < 12, readNatList (runAdd rangeDouble_term n) = rangeDouble n) n hn

theorem attachVal_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
    readNatList (runAdd attachVal_term (natList l)) = attachVal l :=
  forall_small (fun l => readNatList (runAdd attachVal_term (natList l)) = attachVal l) (by decide +kernel) l hlen hx

theorem rangeIndex_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
    readNatList (runAdd rangeIndex_term (natList l)) = rangeIndex l :=
  forall_small (fun l => readNatList (runAdd rangeIndex_term (natList l)) = rangeIndex l) (by decide +kernel) l hlen hx

theorem attachWithSum_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
    runAdd attachWithSum_term (natList l) = attachWithSum l :=
  forall_small (fun l => runAdd attachWithSum_term (natList l) = attachWithSum l) (by decide +kernel) l hlen hx


end TermTests.ToTerm.ListLibrary
