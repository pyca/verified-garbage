module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairScan

/-! # The paired scan retains exactly the first nonzero source word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG

theorem first_keep (m : Mem) (base : Addr) (src start count : Nat) (before : BitVec 32 × BitVec 32)
    (nonzero : ¬(before.1 = 0#32 ∧ before.2 = 0#32)) : first m base src before start count = before := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    unfold first select
    rw [ite_eq_right nonzero]
    exact ih (start + 1)

theorem first_hit (m : Mem) (base : Addr) (src start count index : Nat)
    (lo : start ≤ index) (hi : index < start + count)
    (below : ∀ j, start ≤ j → j < index → pairAt m base (src + 8 * j) = (0#32, 0#32))
    (hit : pairAt m base (src + 8 * index) ≠ (0#32, 0#32)) :
    first m base src (0#32, 0#32) start count = pairAt m base (src + 8 * index) := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change first m base src (pairAt m base (src + 8 * start)) (start + 1) count = _
    by_cases same : start = index
    · subst start
      exact first_keep m base src (index + 1) count _ (fun ⟨a, b⟩ => hit (Prod.ext a b))
    · rw [below start (Nat.le_refl _) (by omega)]
      exact ih (start + 1) (by omega) (by omega) (fun j hj lt => below j (by omega) lt)

end VG.Proof.RsaKeyGen.X86.LowPair
