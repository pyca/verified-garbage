module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # A candidate on ARMv7: the taint analysis of the round's exponent -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate
open VG.Impl.RsaKeyGen.Arm.Key (notS)

theorem copyHm_taint : Cert (copy aHm aCm1) := ⟨_, by taint_decide⟩
theorem tc0_taint : Cert (.block (setS sTc 0)) := ⟨_, by taint_decide⟩
theorem cnt8Tail_taint : Cert (.block [.mov .r1 (.shifted .r1 .lsl 3), .str .r1 .r8 sCnt]) := ⟨_, by taint_decide⟩
theorem copyH1_taint : Cert (copy aH1 aHm) := ⟨_, by taint_decide⟩
theorem copyH2_taint : Cert (copy aH2 aHm) := ⟨_, by taint_decide⟩
theorem mov11_taint : Cert (.block [.mov .r11 (.imm 0)]) := ⟨_, by taint_decide⟩
theorem halfH2_taint : Cert (half aH2) := ⟨_, by taint_decide⟩
theorem bitHm_taint : Cert (.block (bitOf sBit aHm)) := ⟨_, by taint_decide⟩
theorem notAdd_taint : Cert (.block (notS sBit sBit ++ ([.ldr .r2 .r8 sTc, .dp .add .r2 .r2 (.reg .r1),
    .str .r2 .r8 sTc] : List Instr))) := ⟨_, by taint_decide⟩
theorem selHm_taint : Cert (sel aHm aH1 aH2 sBit) := ⟨_, by taint_decide⟩
theorem cntNext_taint : Cert (.block cntNext) := ⟨_, by taint_decide⟩
theorem sigPow_taint : Cert (.block (sigMasks ++ powWord)) := ⟨_, by taint_decide⟩
theorem copyEx_taint : Cert (copy aEx aC) := ⟨_, by taint_decide⟩
theorem halfEx_taint : Cert (half aEx) := ⟨_, by taint_decide⟩
theorem copyH1Ex_taint : Cert (copy aH1 aEx) := ⟨_, by taint_decide⟩
theorem copyH2Ex_taint : Cert (copy aH2 aEx) := ⟨_, by taint_decide⟩
theorem selS1_taint : Cert (sel aEx aH1 aH2 sS1) := ⟨_, by taint_decide⟩
theorem selS2_taint : Cert (sel aEx aH1 aH2 sS2) := ⟨_, by taint_decide⟩
theorem selS3_taint : Cert (sel aEx aH1 aH2 sS3) := ⟨_, by taint_decide⟩
theorem copyE27_taint : Cert (copy (mBase + 27) aEx) := ⟨_, by taint_decide⟩
theorem expTop_taint : Cert (.block expTop) := ⟨_, by taint_decide⟩

end VG.Proof.Dsa.Arm.Prime
