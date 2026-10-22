module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # A candidate on ARMv7: the taint analysis of the results -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

/-- `finish r` after the load of `used`'s pointer. -/
abbrev finTail (r : Nat) : List Instr :=
  [.str .r3 .r2 0, .mov .r1 (.imm 0), .str .r1 .r2 4, .mov .r0 (.imm (BitVec.ofNat 32 r))]

theorem finTail0_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail 0)) hc).isSome =
    true := ⟨_, by taint_decide⟩
theorem finTail1_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail 1)) hc).isSome =
    true := ⟨_, by taint_decide⟩
theorem finTail2_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail 2)) hc).isSome =
    true := ⟨_, by taint_decide⟩
theorem finTail3_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail 3)) hc).isSome =
    true := ⟨_, by taint_decide⟩
theorem mov30_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r3 (.imm 0)]) hc).isSome =
    true := ⟨_, by taint_decide⟩
theorem ldrUsed_taint : Cert (.block [.ldr .r3 .r8 sUsed]) := ⟨_, by taint_decide⟩
theorem setMask_taint : Cert (.block (setS sMask 1)) := ⟨_, by taint_decide⟩
theorem stat0_cmp_taint : Cert (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 0)]) := ⟨_, by taint_decide⟩
theorem stat1_cmp_taint : Cert (.block [.ldr .r1 .r8 sStat, .cmp .r1 (.imm 1)]) := ⟨_, by taint_decide⟩
theorem storeC_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
    (VG.Impl.Rsa.Arm.CrtValues.store aC) hc).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Dsa.Arm.Prime
