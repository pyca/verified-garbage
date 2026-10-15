module

public import VerifiedGarbage.Impl.Bignum.Arm.SecretExp
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Extract a private exponent bit without branching -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp op2_lsr op2_imm dpVal)

theorem secretBitValue_ok (s : State) {base : BitVec 32} {size V : Nat}
    (ws : Workspace s base size) (fits : 204 ≤ size) (ptr : s.gpr .r0 = base) (hv : V < 2 ^ 32)
    (value : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (.block secretBitValue) s fun t => (t.gpr .r11).toNat = V / 128 % 2 ∧
      t.mem = s.mem ∧ Rest [.r11] s t := by
  unfold secretBitValue
  refine wp_ldr (a := off (State.addr base) 200) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read (by omega)) fun u h => ?_
  refine wp_mov (op2_lsr (by decide)) fun v j => ?_
  refine wp_dp (op2_imm (by decide)) fun t l => WP.block_nil ?_
  refine ⟨?_, l.mem.trans (j.mem.trans h.mem),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans (l.rest (by simp)))⟩
  rw [l.gpr, dpVal, j.gpr, h.gpr, value, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow,
    show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

end VG.Proof.Bignum.Arm
