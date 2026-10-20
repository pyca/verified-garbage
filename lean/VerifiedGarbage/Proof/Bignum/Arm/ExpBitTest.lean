module

public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Extract the next public RSA exponent bit from its shifted byte -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp wp_subs op2_lsr op2_imm dpVal)

theorem bit7_word (V : Nat) (hv : V < 2 ^ 32) :
    ((BitVec.ofNat 32 V >>> 7) &&& (1 : BitVec 32) == 0) = decide (V / 128 % 2 = 0) := by
  have value : ((BitVec.ofNat 32 V >>> 7) &&& (1 : BitVec 32)).toNat = V / 128 % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
      Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  by_cases zero : V / 128 % 2 = 0
  · simp only [zero, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [value, zero]; rfl
  · simp only [zero, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro eq
    apply zero
    rw [← value, eq]; rfl

theorem expBitTest_ok (s : State) {base : BitVec 32} {size V : Nat}
    (ws : Workspace s base size) (fits : 204 ≤ size) (ptr : s.gpr .r0 = base) (hv : V < 2 ^ 32)
    (value : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (.block expBitTest) s fun t => t.z = decide (V / 128 % 2 = 0) ∧
      t.mem = s.mem ∧ Rest [.r1] s t := by
  unfold expBitTest
  refine wp_ldr (a := off (State.addr base) 200) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read (by omega)) fun u h => ?_
  refine wp_mov (op2_lsr (by decide)) fun v j => ?_
  refine wp_dp (op2_imm (by decide)) fun z l => ?_
  refine wp_subs (op2_imm (by decide)) fun t q zero => WP.block_nil ?_
  refine ⟨?_, q.mem.trans (l.mem.trans (j.mem.trans h.mem)),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans ((l.rest (by simp)).trans (q.rest (by simp))))⟩
  have subzero : z.gpr .r1 - (0 : BitVec 32) = z.gpr .r1 := BitVec.sub_zero _
  rw [zero, subzero, l.gpr, dpVal, j.gpr, h.gpr, value]
  exact bit7_word V hv

end VG.Proof.Bignum.Arm
