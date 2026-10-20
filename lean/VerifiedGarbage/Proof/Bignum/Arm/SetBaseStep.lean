module

public import VerifiedGarbage.Impl.Bignum.Arm.SetBases
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # One shared-header pointer store -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_subs op2_reg op2_imm dpVal)

theorem setBaseStep_ok (s : State) (a : Addr)
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = a + BitVec.ofNat 64 4)
    (wa : InRegions s.wr a 4) (wb : InRegions s.wr (a + BitVec.ofNat 64 4) 4)
    (zero : s.gpr .r3 = 0) :
    WP isa (.block setBaseStep) s fun t =>
      t.mem = s.mem.writeW a (State.addr (s.gpr .r4)) ∧
      t.gpr .r0 = s.gpr .r0 + 8 ∧ t.gpr .r4 = s.gpr .r4 + s.gpr .r5 ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .r4, .lr] s t := by
  rw [setBaseStep, WP.block_append_iff]
  refine WP.mono (store64_ok s .r4 .r3 .r0 0 a (by decide) pa pb wa wb) ?_
  rintro u ⟨mem, rest⟩
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u3 z3 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u3.mem, u2.mem, u1.mem, mem, zero, zero_high_addr]
  · rw [u3.other .r0 (by decide), u2.other .r0 (by decide), u1.gpr, dpVal, rest.gpr .r0 (by simp)]
  · rw [u3.other .r4 (by decide), u2.gpr, dpVal, u1.other .r4 (by decide), u1.other .r5 (by decide),
      rest.gpr .r4 (by simp), rest.gpr .r5 (by simp)]
  · rw [u3.gpr, u2.other .lr (by decide), u1.other .lr (by decide), rest.gpr .lr (by simp)]
  · rw [z3, u2.other .lr (by decide), u1.other .lr (by decide), rest.gpr .lr (by simp)]
  · exact (rest.mono (by simp)).trans ((u1.rest (by simp)).trans
      ((u2.rest (by simp)).trans (u3.rest (by simp))))

end VG.Proof.Bignum.Arm
