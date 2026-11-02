module

public import VerifiedGarbage.Impl.Bignum.Arm.ReduceOperand
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # Exact reduction through Montgomery encoding and decoding -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem reduceOperand_ok (s : State) {base : BitVec 32} {len w o M : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ho0 : o ≠ 0) (ho7 : o ≠ 7)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M)
    (one : numAt s.mem (State.addr base) w 7 = 1) :
    WP isa (reduceOperand o) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr base) w o % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  rw [reduceOperand, WP.seq_iff]
  refine WP.mono (montEncode_ok s h ho ho ho0 modulus odd r2) ?_
  rintro u ⟨readyU, modU, encoded, keepsU, frameU, restU⟩
  have oneU := (keeps_array_num keepsU fits op7 (Ne.symm ho7)).trans one
  refine WP.mono (montOp_ok u readyU ho ho op7 ho0 (by rw [oneU]; exact readyU.modulus)) ?_
  rintro t ⟨ready, modT, bound, value, keepsT, frameT, restT⟩
  rw [modU] at modT bound value
  rw [oneU, Nat.mul_one, encoded, Nat.mod_mod] at value
  have reduced := mont_cancel (coprime_pow2 odd (64 * w)) value
  rw [Nat.mod_eq_of_lt bound] at reduced
  exact ⟨ready, modT, reduced, fun i hi sep => (keepsT i hi sep).trans (keepsU i hi sep),
    frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
