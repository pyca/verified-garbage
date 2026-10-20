module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # A candidate on ARMv7: the taint analysis of `gcd(c − 1, e)` -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate
open VG.Impl.RsaKeyGen.Arm.Key (isOne)

theorem subCm1_taint : Cert (sub3 aCm1 aC aOne) := ⟨_, by taint_decide⟩
theorem bitEo_taint : Cert (.block (bitOf sEo aE)) := ⟨_, by taint_decide⟩
theorem eqE1_taint : Cert (eqS sE1 aE aOne aTmp) := ⟨_, by taint_decide⟩
theorem isEo_taint : Cert (.block (isOne sEo)) := ⟨_, by taint_decide⟩
theorem isE1_taint : Cert (.block (isOne sE1)) := ⟨_, by taint_decide⟩
theorem isG_taint : Cert (.block (isOne sG)) := ⟨_, by taint_decide⟩
theorem g1_taint : Cert (.block (setS sG 1)) := ⟨_, by taint_decide⟩
theorem g0_taint : Cert (.block (setS sG 0)) := ⟨_, by taint_decide⟩
theorem copyME_taint : Cert (copy aM aE) := ⟨_, by taint_decide⟩
theorem copy0Cm1_taint : Cert (copy 0 aCm1) := ⟨_, by taint_decide⟩
theorem copy2One_taint : Cert (copy 2 aOne) := ⟨_, by taint_decide⟩
theorem eqG_taint : Cert (eqS sG 1 aOne aTmp) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Cand
