import VerifiedGarbage.Proof.Framework.Semantics

/-! A kernel-checkable lookup tree for untrusted forwarding certificates.
Lookup soundness only needs every stored entry to satisfy the predicate;
it does not assume that the tree is sorted or balanced. -/
namespace VG.Proof.Weierstrass.AArch64.Forward

inductive Tree (α : Type) where
  | empty : Tree α
  | node (key : Nat) (value : α) (left right : Tree α) : Tree α

namespace Tree

def lookup {α : Type} (key : Nat) : Tree α → Option α
  | .empty => none
  | .node k v left right =>
    if key=k then some v else if key<k then lookup key left else lookup key right

def all {α : Type} (P : Nat → α → Bool) : Tree α → Bool
  | .empty => true
  | .node k v left right => P k v && all P left && all P right

/-- Even malformed or unsorted trees cannot return a value that failed validation. -/
theorem lookup_all {α : Type} {P : Nat → α → Bool} {tree : Tree α} {key : Nat} {value : α}
    (ha : all P tree=true) (hl : lookup key tree=some value) : P key value=true := by
  induction tree with
  | empty => cases hl
  | node k v left right ihl ihr =>
    simp only [all,Bool.and_eq_true] at ha
    by_cases he : key=k
    · subst key
      simp only [lookup,ite_true,Option.some.injEq] at hl
      subst value
      exact ha.1.1
    · by_cases ht : key<k
      · rw [lookup,ite_eq_right he,ite_eq_left ht] at hl
        exact ihl ha.1.2 hl
      · rw [lookup,ite_eq_right he,ite_eq_right ht] at hl
        exact ihr ha.2 hl

end Tree
end VG.Proof.Weierstrass.AArch64.Forward
