module

public import VerifiedGarbage.Impl.Bignum.Arm.CompareWords
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! One wordwise XOR/OR comparison step preserves memory. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_subs op2_imm op2_reg dpVal)

theorem compareWordStep_ok (s : State) (a b : Addr)
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = b)
    (ra : InRegions (s.rd ++ s.wr) a 4) (rb : InRegions (s.rd ++ s.wr) b 4) :
    WP isa (.block compareWordStep) s fun t => t.mem = s.mem ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .r1 = s.gpr .r1 + 4 ∧
      t.gpr .r2 = s.gpr .r2 ||| (s.mem.readW a 32 ^^^ s.mem.readW b 32) ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧
      Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  unfold compareWordStep
  refine wp_ldr (by decide) pa ra fun s1 u1 => ?_
  refine wp_ldr (a := b) (by decide) (by rw [u1.other .r1 (by decide)]; exact pb)
    (by rw [u1.rd, u1.wr]; exact rb) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u7 z7 => WP.block_nil ?_
  refine ⟨u7.mem.trans (u6.mem.trans (u5.mem.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u7.other .r0 (by decide), u6.other .r0 (by decide), u5.gpr, dpVal,
      u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  · rw [u7.other .r1 (by decide), u6.gpr, dpVal, u5.other .r1 (by decide),
      u4.other .r1 (by decide), u3.other .r1 (by decide), u2.other .r1 (by decide), u1.other .r1 (by decide)]
  · rw [u7.other .r2 (by decide), u6.other .r2 (by decide), u5.other .r2 (by decide), u4.gpr, dpVal,
      u3.other .r2 (by decide), u2.other .r2 (by decide), u1.other .r2 (by decide),
      u3.gpr, dpVal, u2.other .r3 (by decide), u1.gpr, u2.gpr, u1.mem]
  · rw [u7.gpr, u6.other .lr (by decide), u5.other .lr (by decide), u4.other .lr (by decide),
      u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [z7, u6.other .lr (by decide), u5.other .lr (by decide), u4.other .lr (by decide),
      u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide)))))))
end VG.Proof.Bignum.Arm
