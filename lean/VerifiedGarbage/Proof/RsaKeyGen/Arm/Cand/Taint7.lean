module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the taint analysis of Miller–Rabin -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate
open VG.Impl.RsaKeyGen.Arm.Key (andNotS isOne)

theorem mrInit_taint : Cert (.block mrInit) := ⟨_, by taint_decide⟩
theorem avUsed_taint : Cert (.block [.ldr .r2 .r8 sUsed, .dp .sub .r1 .r1 (.reg .r2)]) := ⟨_, by taint_decide⟩
theorem stat0_taint : Cert (.block (setS sStat 0)) := ⟨_, by taint_decide⟩
theorem stat3_taint : Cert (.block (setS sStat 3)) := ⟨_, by taint_decide⟩
theorem wl1_taint : Cert (.block [.ldr .r1 .r8 sUsed, .dp .add .r4 .r4 (.reg .r1)]) := ⟨_, by taint_decide⟩
theorem wl2_taint : Cert (.block [.dp .add .r1 .r1 (.reg .r6), .str .r1 .r8 sUsed]) := ⟨_, by taint_decide⟩
theorem ltA_taint : Cert (seqs (ltS sA aX aTwo)) := ⟨_, by taint_decide⟩
theorem ltB_taint : Cert (seqs (ltS sBb aX aCm1)) := ⟨_, by taint_decide⟩
theorem andNotU_taint : Cert (.block (andNotS sU sA sBb)) := ⟨_, by taint_decide⟩
theorem copyXf_taint : Cert (copy aXf aX) := ⟨_, by taint_decide⟩
theorem orTwoXf_taint : Cert (.block (orTwo aXf)) := ⟨_, by taint_decide⟩
theorem clrTopBitXf_taint : Cert (.block (clrTopBit aXf)) := ⟨_, by taint_decide⟩
theorem selX_taint : Cert (sel aH1 aXf aX sU) := ⟨_, by taint_decide⟩
theorem copy1X_taint : Cert (copy (mBase + 1) aH1) := ⟨_, by taint_decide⟩
theorem wsTail_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r2 (.shifted .r2 .lsr 3),
    .mov .r3 (.imm 21), .mul .r2 .r2 .r3, .dp .add .r2 .r2 (.imm 30), .dp .sub .r1 .r1 (.reg .r2)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem strF_taint : Cert (.block [.str .r0 .r8 sF]) := ⟨_, by taint_decide⟩
theorem isOneF_taint : Cert (.block (isOne sF)) := ⟨_, by taint_decide⟩
theorem onPass_taint : Cert (.block onPass) := ⟨_, by taint_decide⟩
theorem cmp4_taint : Cert (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 4)]) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Cand
