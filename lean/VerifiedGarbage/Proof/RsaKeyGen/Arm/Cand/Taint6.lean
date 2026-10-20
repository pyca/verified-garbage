module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # A candidate on ARMv7: the taint analysis of Montgomery multiplication's setup -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

theorem montHead_taint : Cert (.block (ptr .r0 mBase ++ ([.dp .sub .r0 .r0 (.imm 256)] : List Instr))) := ⟨_, by taint_decide⟩
theorem ctxW_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8]) (.block ctxW) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem clrTopC_taint : Cert (.block (clrTop mBase)) := ⟨_, by taint_decide⟩
theorem strideW_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r7]) (.block strideW) hc).isSome =
    true := ⟨_, by taint_decide⟩
theorem copy1One_taint : Cert (copy (mBase + 1) aOne) := ⟨_, by taint_decide⟩
theorem clrTop1_taint : Cert (.block (clrTop (mBase + 1))) := ⟨_, by taint_decide⟩
theorem copy9_taint : Cert (copy (mBase + 9) (mBase + 1)) := ⟨_, by taint_decide⟩
theorem sub10_taint : Cert (sub3 (mBase + 10) mBase (mBase + 9)) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Cand
