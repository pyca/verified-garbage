module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # One masked private-result byte and clearing of its temporary source -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked
open VG.Proof.X25519.Arm (Rest wp_ldrb wp_strb wp_dp wp_subs op2_imm op2_reg dpVal)

theorem releaseStep_ok (s : State) (src dst : Addr)
    (ps : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = src)
    (pd : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = dst)
    (read : InRegions (s.rd ++ s.wr) src 1) (write : InRegions s.wr dst 1) (clear : InRegions s.wr src 1)
    (zeroReg : s.gpr .r12 = 0) :
    WP isa (.block releaseStep) s fun t =>
      t.mem = (s.mem.writeW dst (s.mem src &&& (s.gpr .r2).setWidth 8)).writeW src (0 : Byte) ∧
      t.gpr .r0 = s.gpr .r0 + 1 ∧ t.gpr .r1 = s.gpr .r1 + 1 ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .r1, .r3, .lr] s t := by
  unfold releaseStep
  refine wp_ldrb (by decide) ps read fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_strb (a := dst) (by decide)
    (by rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact pd)
    (by rw [u2.wr, u1.wr]; exact write) fun s3 u3 => ?_
  refine wp_strb (a := src) (by decide)
    (by rw [u3.gpr, u2.other .r1 (by decide), u1.other .r1 (by decide)]; exact ps)
    (by rw [u3.wr, u2.wr, u1.wr]; exact clear) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u7 z7 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem,
      u3.gpr, u2.other .r12 (by decide), u1.other .r12 (by decide), zeroReg,
      u2.gpr, dpVal, u1.gpr, u1.other .r2 (by decide), BitVec.setWidth_and,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
    rfl
  · rw [u7.other .r0 (by decide), u6.other .r0 (by decide), u5.gpr, dpVal, u4.gpr, u3.gpr,
      u2.other .r0 (by decide), u1.other .r0 (by decide)]
  · rw [u7.other .r1 (by decide), u6.gpr, dpVal, u5.other .r1 (by decide), u4.gpr, u3.gpr,
      u2.other .r1 (by decide), u1.other .r1 (by decide)]
  · rw [u7.gpr, u6.other .lr (by decide), u5.other .lr (by decide), u4.gpr, u3.gpr,
      u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [z7, u6.other .lr (by decide), u5.other .lr (by decide), u4.gpr, u3.gpr,
      u2.other .lr (by decide), u1.other .lr (by decide)]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest _).trans
      ((u4.rest _).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp)))))))
end VG.Proof.Rsa.Arm
