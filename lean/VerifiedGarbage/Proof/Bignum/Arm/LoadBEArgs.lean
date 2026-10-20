module

public import VerifiedGarbage.Impl.Bignum.Arm.LoadBE
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Set pointers for RSA byte reversal -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem loadBEreverseArgs_ok (s : State) {k : Nat} (hk : 0 < k)
    (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (.block loadBEreverseArgs) s fun t =>
      t.gpr .r0 = s.gpr .r5 ∧ t.gpr .r1 = s.gpr .r4 + BitVec.ofNat 32 (k - 1) ∧
      t.gpr .lr = BitVec.ofNat 32 k ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .lr] s t := by
  unfold loadBEreverseArgs
  refine wp_mov (op2_reg _ _) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_reg _ _) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide), u1.gpr]
  · rw [u4.other .r1 (by decide), u3.gpr, dpVal, u2.gpr, dpVal,
      u1.other .r4 (by decide), u1.other .r6 (by decide), count]
    change s.gpr .r4 + BitVec.ofNat 32 k - BitVec.ofNat 32 1 = _
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega)]
  · rw [u4.gpr, u3.other .r6 (by decide), u2.other .r6 (by decide), u1.other .r6 (by decide), count]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))

end VG.Proof.Bignum.Arm
