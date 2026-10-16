module

public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpBit
public import VerifiedGarbage.Proof.Bignum.Arm.SelectPowerCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
meta import VerifiedGarbage.Impl.Bignum.Arm.SecretExp
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A private exponent bit has the same trace even when both exponents differ -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (Operand arrAt)

theorem secretBitValue_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) : WP isa (.block secretBitValue) s (ArithmeticReady base len w) := by
  have size : 204 ≤ 8 * len := by
    have := h.layout.2.2.1
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at this
    omega
  refine WP.mono (secretBitValue_ok s h.workspace size h.ptr
    (s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32).isLt (by simp)) ?_
  rintro t ⟨_, mem, rest⟩
  exact h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)

theorem secretExpBit_ct {base : BitVec 32} {len w M1 M2 x1 x2 E1 E2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => ExpState base len w M1 x1 E1 s ∧
      ExpState base len w M2 x2 E2 t ∧ s.sp = t.sp) secretExpBit (fun _ _ => True) := by
  let P := fun (s t : State) => ExpState base len w M1 x1 E1 s ∧
    ExpState base len w M2 x2 E2 t ∧ s.sp = t.sp
  let Q := fun (s t : State) => s.sp = t.sp ∧ ExpState base len w M1 x1 (2 * E1) s ∧
    ExpState base len w M2 x2 (2 * E2) t
  let R := fun (s t : State) => s.sp = t.sp ∧ ArithmeticReady base len w s ∧ ArithmeticReady base len w t
  have square : RelCT isa P (montOp 6 6 6) (fun _ _ => True) := by
    apply (montOp_ct (base := base) (o := 6) (a := 6) (b := 6)
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) fit).mono
      (fun _ _ h => ⟨⟨h.1.ready, by rw [h.1.modulus]; exact h.1.powerBound⟩,
        ⟨h.2.1.ready, by rw [h.2.1.modulus]; exact h.2.1.powerBound⟩, h.2.2⟩) (fun _ _ h => h)
  have squared := (relCT_keep_sp square (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨WP.mono (exp_square_ok s h.1) (fun _ j => j.1),
      WP.mono (exp_square_ok t h.2.1) (fun _ j => j.1)⟩)
  have multiply : RelCT isa Q (montOp 1 6 5) (fun _ _ => True) := by
    apply (montOp_ct (base := base) (o := 1) (a := 6) (b := 5)
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) fit).mono
      (fun _ _ h => ⟨⟨h.2.1.ready, by rw [h.2.1.modulus]; exact h.2.1.inputBound⟩,
        ⟨h.2.2.ready, by rw [h.2.2.modulus]; exact h.2.2.inputBound⟩, h.1⟩) (fun _ _ h => h)
  have multiplied := (relCT_keep_sp multiply (fun _ _ h => h.1)).wp
    (fun s t h => ⟨WP.mono (secretMultiply_ok s h.2.1) (fun _ j => j.1.ready),
      WP.mono (secretMultiply_ok t h.2.2) (fun _ j => j.1.ready)⟩)
  have bit : RelCT isa R (.block secretBitValue) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.ptr.trans h.2.2.ptr.symm
  have selected := (relCT_keep_sp bit (fun _ _ h => h.1)).wp
    (fun s t h => ⟨secretBitValue_ready s h.2.1, secretBitValue_ready t h.2.2⟩)
  have selection : RelCT isa R selectPower (fun _ _ => True) :=
    selectPower_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)
  exact squared.seq (multiplied.seq (selected.seq selection))

end VG.Proof.Bignum.Arm
