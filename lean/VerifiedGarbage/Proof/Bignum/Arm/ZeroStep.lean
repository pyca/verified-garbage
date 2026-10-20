module

public import VerifiedGarbage.Impl.Bignum.Arm.Zero
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! # One packed-word zeroing step -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_str wp_dp wp_subs op2_imm dpVal)

theorem zeroStep_ok (s : State) (a : Addr)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (wa : InRegions s.wr a 4) (hz : s.gpr .r3 = 0) :
    WP isa (.block zeroStep) s fun t =>
      t.mem = s.mem.writeW a (0 : BitVec 32) ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .lr] s t := by
  unfold zeroStep
  refine wp_str (a := a) (by decide) ha wa fun s1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_subs (op2_imm (by decide)) fun s3 u3 hc => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u3.mem, u2.mem, u1.mem, hz]
  · rw [u3.other .r0 (by decide), u2.gpr, dpVal, u1.gpr]
  · rw [u3.gpr, u2.other .lr (by decide), u1.gpr]
  · rw [hc, u2.other .lr (by decide), u1.gpr]
  · exact (u1.rest _).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))

end VG.Proof.Bignum.Arm
