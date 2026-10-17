module

public import VerifiedGarbage.Proof.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.WideProductBodyCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Wide multiplication leaks no operand values -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem wideProduct_ct {s01 s02 : State} {base : BitVec 32} {size o a b m n : Nat}
    (ctx1 : WideProductCtx s01 base size o a b m n) (ctx2 : WideProductCtx s02 base size o a b m n) :
    RelCT isa (fun s t => WideProductInv s01 base o a b m n 0 s ∧
      WideProductInv s02 base o a b m n 0 t ∧ s.sp = t.sp) wideProduct (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ i, i + k = m ∧ 0 < k ∧
    WideProductInv s01 base o a b m n i s ∧ WideProductInv s02 base o a b m n i t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) wideProductBody fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ j, j < k ∧ I j s t) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨i, ik, hk, hs, ht, sp⟩ := h
    have hi : i < m := by omega
    have ct := relCT_keep_sp (wideProductBody_ct ctx1 ctx2 hi) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u v ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1⟩ := wideProductBody_ok s ctx1 hs hi
    obtain ⟨_, _, run2, next2, zero2⟩ := wideProductBody_ok t ctx2 ht hi
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_ ) = some (!_ )
      rw [zero1, zero2]
    · intro again
      have notLast : i + 1 ≠ m := by
        intro last
        change some (!_ ) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, i + 1, by omega, by omega, next1, next2, sp'⟩
  exact (RelCT.loop I step m).mono
    (fun _ _ h => ⟨0, by omega, ctx1.positiveA, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
