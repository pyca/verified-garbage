module

public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Exact memory effect of masking one output byte -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldrb wp_strb wp_dp wp_subs op2_imm op2_reg dpVal)

theorem maskByteStep_ok (s : State) (dst : Addr)
    (pd : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = dst)
    (read : InRegions (s.rd ++ s.wr) dst 1) (write : InRegions s.wr dst 1) :
    WP isa (.block maskByteStep) s fun t =>
      t.mem = s.mem.writeW dst (s.mem dst &&& (s.gpr .r2).setWidth 8) ∧
      t.gpr .r0 = s.gpr .r0 + 1 ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧
      Rest [.r0, .r1, .lr] s t := by
  unfold maskByteStep
  refine wp_ldrb (by decide) pd read fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_strb (a := dst) (by decide)
    (by rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact pd)
    (by rw [u2.wr, u1.wr]; exact write) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u5 z5 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u2.gpr, dpVal,
      u1.gpr, u1.other .r2 (by decide), BitVec.setWidth_and,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  · rw [u5.other .r0 (by decide), u4.gpr, dpVal, u3.gpr,
      u2.other .r0 (by decide), u1.other .r0 (by decide)]
  · rw [u5.gpr, u4.other .lr (by decide), u3.gpr,
      u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [z5, u4.other .lr (by decide), u3.gpr,
      u2.other .lr (by decide), u1.other .lr (by decide)]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest _).trans
      ((u4.rest (by simp)).trans (u5.rest (by simp)))))

end VG.Proof.Bignum.Arm
