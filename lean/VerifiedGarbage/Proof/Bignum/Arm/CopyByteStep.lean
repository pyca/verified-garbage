module

public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # One copied byte and its exact memory effect -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldrb wp_strb wp_dp wp_subs op2_imm dpVal)

theorem copyByteStep_ok (s : State) (src dst : Addr)
    (ps : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = src)
    (pd : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = dst)
    (read : InRegions (s.rd ++ s.wr) src 1) (write : InRegions s.wr dst 1) :
    WP isa (.block copyByteStep) s fun t =>
      t.mem = s.mem.writeW dst (s.mem src) ∧
      t.gpr .r0 = s.gpr .r0 + 1 ∧ t.gpr .r1 = s.gpr .r1 + 1 ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧
      Rest [.r0, .r1, .r2, .lr] s t := by
  unfold copyByteStep
  refine wp_ldrb (by decide) ps read fun s1 u1 => ?_
  refine wp_strb (a := dst) (by decide) (by rw [u1.other .r0 (by decide)]; exact pd)
    (by rw [u1.wr]; exact write) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u5 z5 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u1.gpr, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  · rw [u5.other .r0 (by decide), u4.other .r0 (by decide), u3.gpr, dpVal, u2.gpr, u1.other .r0 (by decide)]
  · rw [u5.other .r1 (by decide), u4.gpr, dpVal, u3.other .r1 (by decide), u2.gpr, u1.other .r1 (by decide)]
  · rw [u5.gpr, u4.other .lr (by decide), u3.other .lr (by decide), u2.gpr, u1.other .lr (by decide)]
  · rw [z5, u4.other .lr (by decide), u3.other .lr (by decide), u2.gpr, u1.other .lr (by decide)]
  · exact (u1.rest (by simp)).trans ((u2.rest _).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans (u5.rest (by simp)))))

end VG.Proof.Bignum.Arm
