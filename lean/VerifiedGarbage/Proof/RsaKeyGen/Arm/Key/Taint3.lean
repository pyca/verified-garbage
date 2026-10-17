module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: the pieces of the key the taint analysis checks -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key

-- `qInv`
theorem bitPo_taint : Cert (.block (bitOf sPo aP)) := ⟨_, by taint_decide⟩
theorem ltP3_taint : Cert (seqs (ltS sP3 aP aThree)) := ⟨_, by taint_decide⟩
theorem qg_taint : Cert (.block (andNotS sQg sP3 sPo)) := ⟨_, by taint_decide⟩
theorem selQM_taint : Cert (sel aTmp2 aThree aP sQg) := ⟨_, by taint_decide⟩
theorem q0_taint : Cert (copy 0 aQ) := ⟨_, by taint_decide⟩
theorem eqGq_taint : Cert (eqS sGq 1 aOne aTmp) := ⟨_, by taint_decide⟩
theorem qi_taint : Cert (copy aQi 3) := ⟨_, by taint_decide⟩

-- `dP` and `dQ`
theorem zPm_taint : Cert (eqS sZ aPm aZero aTmp) := ⟨_, by taint_decide⟩
theorem selPm1_taint : Cert (sel aTmp2 aPm aOne sZ) := ⟨_, by taint_decide⟩
theorem zQm_taint : Cert (eqS sZ aQm aZero aTmp) := ⟨_, by taint_decide⟩
theorem selQm1_taint : Cert (sel aTmp2 aQm aOne sZ) := ⟨_, by taint_decide⟩
theorem qdD_taint : Cert (copy aQd aD) := ⟨_, by taint_decide⟩
theorem dvT2_taint : Cert (copy aDv aTmp2) := ⟨_, by taint_decide⟩
theorem dpDr_taint : Cert (copy aDP aDr) := ⟨_, by taint_decide⟩
theorem dqDr_taint : Cert (copy aDQ aDr) := ⟨_, by taint_decide⟩

-- `n`
theorem myQ_taint : Cert (copy aMy aQ) := ⟨_, by taint_decide⟩
theorem mxP_taint : Cert (copy aMx aP) := ⟨_, by taint_decide⟩
theorem nMa_taint : Cert (copy aN aMa) := ⟨_, by taint_decide⟩

-- The mask
theorem ltTop_taint : Cert (seqs (ltS sTop aN aTop)) := ⟨_, by taint_decide⟩
theorem bitQo_taint : Cert (.block (bitOf sQo aQ)) := ⟨_, by taint_decide⟩
theorem ltE3_taint : Cert (seqs (ltS sE3 aE aThree)) := ⟨_, by taint_decide⟩
theorem ltEv_taint : Cert (seqs (ltS sEv aE aC33)) := ⟨_, by taint_decide⟩
theorem m1_taint : Cert (.block (andNotS sMask sTop sOk)) := ⟨_, by taint_decide⟩
theorem m2_taint : Cert (.block (andS sMask sMask sGq)) := ⟨_, by taint_decide⟩
theorem m3_taint : Cert (.block (andS sMask sMask sPo)) := ⟨_, by taint_decide⟩
theorem m4_taint : Cert (.block (andS sMask sMask sQo)) := ⟨_, by taint_decide⟩
theorem m5_taint : Cert (.block (andS sMask sMask sEo)) := ⟨_, by taint_decide⟩
theorem m6_taint : Cert (.block (andNotS sE3 sE3 sEv)) := ⟨_, by taint_decide⟩
theorem m7_taint : Cert (.block (andS sMask sMask sE3)) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Key
