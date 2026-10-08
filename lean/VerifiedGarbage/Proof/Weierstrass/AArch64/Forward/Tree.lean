import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Data
import VerifiedGarbage.Proof.Framework.Semantics

/-! A kernel-checkable lookup tree for untrusted forwarding certificates.
Lookup soundness only needs every stored entry to satisfy the predicate;
it does not assume that the tree is sorted or balanced. -/
namespace VG.Proof.Weierstrass.AArch64.Forward

namespace Tree

/-- Even malformed or unsorted trees cannot return a value that failed validation. -/
theorem lookup_all {α : Type} {P : Nat → α → Bool} {tree : Tree α} {key : Nat} {value : α}
    (ha : all P tree=true) (hl : lookup key tree=some value) : P key value=true := by
  induction tree with
  | empty => cases hl
  | node k v left right ihl ihr =>
    simp only [all,Bool.and_eq_true] at ha
    simp only [lookup, cond_eq_ite, Nat.beq_eq, Nat.blt_eq] at hl
    split at hl
    · rename_i he
      subst key
      cases hl
      exact ha.1.1
    · split at hl
      · exact ihl ha.1.2 hl
      · exact ihr ha.2 hl

end Tree
end VG.Proof.Weierstrass.AArch64.Forward
