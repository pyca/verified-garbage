module

public import VerifiedGarbage.Proof.Bignum.Arm.ExponentState
meta import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Validation scans only public exponent bytes and public lengths -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem exponentLoop_ct {ep : BitVec 32} {eb : List Byte} (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExponentState ep eb 0 s ∧ ExponentState ep eb 0 t)
      (.loop exponentByte .ne) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb.length ∧ 0 < k ∧
    ExponentState ep eb j s ∧ ExponentState ep eb j t
  have step : ∀ k, RelCT isa (I k) exponentByte fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨j, jk, hk, hs, ht⟩ := h
    have hj : j < eb.length := by omega
    have trace := (exponentByte_ct s t tr1 tr2 u v ⟨hs.input hj, ht.input hj⟩ e1 e2).1
    obtain ⟨_, _, run1, next1, zero1⟩ := exponentState_step s hs hj
    obtain ⟨_, _, run2, next2, zero2⟩ := exponentState_step t ht hj
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_ ) = some (!_ )
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ eb.length := by
        intro last
        change some (!_ ) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, next2⟩
  exact (RelCT.loop I step eb.length).mono (fun _ _ h => ⟨0, by omega, positive, h.1, h.2⟩) (fun _ _ h => h)

def ExponentInput (ep : BitVec 32) (eb : List Byte) (s : State) : Prop :=
  ExponentBuffer ep eb s ∧ s.gpr .r1 = ep ∧ s.gpr .lr = BitVec.ofNat 32 eb.length

theorem exponentScan_ct {ep : BitVec 32} {eb : List Byte} (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExponentInput ep eb s ∧ ExponentInput ep eb t)
      exponentScan (fun _ _ => True) := by
  have init : RelCT isa (fun s t => ExponentInput ep eb s ∧ ExponentInput ep eb t)
      (.block [.mov .r3 (.imm 0), .mov .r4 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : ExponentInput ep eb s) :
      WP isa (.block [.mov .r3 (.imm 0), .mov .r4 (.imm 0)]) s (ExponentState ep eb 0) :=
    exponentInit_ready s h.1 h.2.1 h.2.2
  exact (pair_posts init wp).seq (exponentLoop_ct positive)

end VG.Proof.Bignum.Arm
