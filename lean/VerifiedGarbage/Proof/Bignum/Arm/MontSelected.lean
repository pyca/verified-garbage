module

public import VerifiedGarbage.Impl.Bignum.Arm.MontSelected
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT

/-! The specialized square and general product meet the same arithmetic,
frame and constant-time obligations. Operand indices are program constants. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem selectedMontOp_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (selectedMontOp o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold selectedMontOp
  split
  · rename_i equal
    subst b
    exact squareOp_ok s h ho ha ho0 operand
  · exact montOp_ok s h ho ha hb ho0 operand

theorem selectedMontOp_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (fit : Proof.Rsa.Mont.arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧
        s.sp = t.sp)
      (selectedMontOp o a b) (fun _ _ => True) := by
  unfold selectedMontOp
  split
  · rename_i equal
    subst b
    exact squareOp_ct ho ha
  · exact montOp_ct ho ha hb fit

end VG.Proof.Bignum.Arm
