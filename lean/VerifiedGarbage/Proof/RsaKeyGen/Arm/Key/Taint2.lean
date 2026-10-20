module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # An RSA key on ARMv7: the pieces of `d` and of the status the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key

-- `e = 1`
theorem eqG1_taint : Cert (eqS sG aL aOne aTmp) := ⟨_, by taint_decide⟩
theorem notOk_taint : Cert (.block (notS sOk sG)) := ⟨_, by taint_decide⟩
theorem dOne_taint : Cert (copy aD aOne) := ⟨_, by taint_decide⟩

-- `e` odd
theorem mE_taint : Cert (copy aM aE) := ⟨_, by taint_decide⟩
theorem l0_taint : Cert (copy 0 aL) := ⟨_, by taint_decide⟩
theorem eqG_taint : Cert (eqS sG 1 aOne aTmp) := ⟨_, by taint_decide⟩
theorem ltL2_taint : Cert (seqs (ltS sL2 aL aTwo)) := ⟨_, by taint_decide⟩
theorem okOdd_taint : Cert (.block (andNotS sOk sL2 sG)) := ⟨_, by taint_decide⟩
theorem tt_taint : Cert (sub3 aTt aE 3) := ⟨_, by taint_decide⟩
theorem myT_taint : Cert (copy aMy aTt) := ⟨_, by taint_decide⟩
theorem mxL_taint : Cert (copy aMx aL) := ⟨_, by taint_decide⟩
theorem maOne_taint : Cert (copy aMa aOne) := ⟨_, by taint_decide⟩
theorem qdMa_taint : Cert (copy aQd aMa) := ⟨_, by taint_decide⟩
theorem dvE_taint : Cert (copy aDv aE) := ⟨_, by taint_decide⟩
theorem hdrQd_taint : Cert (.block (VG.Impl.Rsa.Arm.Recover.clrW aDv ++
    VG.Impl.Rsa.Arm.CrtValues.divHdr aQd aDr aDv aDt)) := ⟨_, by taint_decide⟩
theorem dQd_taint : Cert (copy aD aQd) := ⟨_, by taint_decide⟩

-- `e` even
theorem bitLo_taint : Cert (.block (bitOf sLo aL)) := ⟨_, by taint_decide⟩
theorem ltL3_taint : Cert (seqs (ltS sL3 aL aThree)) := ⟨_, by taint_decide⟩
theorem good_taint : Cert (.block (andNotS sGood sL3 sLo)) := ⟨_, by taint_decide⟩
theorem selME_taint : Cert (sel aTmp2 aThree aL sGood) := ⟨_, by taint_decide⟩
theorem e0_taint : Cert (copy 0 aE) := ⟨_, by taint_decide⟩
theorem okEven_taint : Cert (.block (andS sOk sGood sG)) := ⟨_, by taint_decide⟩
theorem d3_taint : Cert (copy aD 3) := ⟨_, by taint_decide⟩

-- `d` too small
theorem cOne_taint : Cert (copy aC aOne) := ⟨_, by taint_decide⟩
theorem cHi_taint : Cert (.block (setHi aC 1 8 1)) := ⟨_, by taint_decide⟩
theorem ltSm_taint : Cert (seqs (ltS sSm aD aC)) := ⟨_, by taint_decide⟩
theorem fl_taint : Cert (.block (andS sFl sSm sOk)) := ⟨_, by taint_decide⟩
theorem isFl_taint : Cert (.block (isOne sFl)) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Key
