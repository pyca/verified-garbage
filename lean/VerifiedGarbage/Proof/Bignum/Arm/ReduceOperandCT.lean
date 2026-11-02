module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.ReduceOperand
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Packed operand reduction does not reveal the modulus or operand -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)

structure ReduceOperandReady (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  r2bound : numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0
  onebound : numAt s.mem (State.addr base) w 7 < numAt s.mem (State.addr base) w 0

theorem reduceOperand_ct {base : BitVec 32} {len w o : Nat}
    (ho : Operand o) (ho0 : o ≠ 0) (ho7 : o ≠ 7) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => ReduceOperandReady base len w s ∧ ReduceOperandReady base len w t ∧ s.sp = t.sp)
      (reduceOperand o) (fun _ _ => True) := by
  let P := ReduceOperandReady base len w
  let Q := fun s : State => ArithmeticReady base len w s ∧
    numAt s.mem (State.addr base) w 7 < numAt s.mem (State.addr base) w 0
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have encode : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
      (montOp o o 4) (fun _ _ => True) :=
    (montOp_ct ho ho op4 fit).mono (fun _ _ h => ⟨⟨h.1.ready, h.1.r2bound⟩,
      ⟨h.2.1.ready, h.2.1.r2bound⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (montOp o o 4) s Q := by
    refine WP.mono (montOp_ok s h.ready ho ho op4 ho0 h.r2bound) ?_
    rintro t ⟨ready, modulus, _, _, keeps, _, _⟩
    have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
    have one := keeps_array_num keeps fits op7 (Ne.symm ho7)
    exact ⟨ready, by rw [one, modulus]; exact h.onebound⟩
  have encoded := (relCT_keep_sp encode (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact encoded.seq ((montOp_ct ho ho op7 fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
