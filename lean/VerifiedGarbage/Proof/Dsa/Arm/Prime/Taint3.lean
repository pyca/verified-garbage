module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint0
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # A candidate on ARMv7: the taint analysis of `gcd(c − 1, e)` -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate
open VG.Impl.RsaKeyGen.Arm.Key (isOne)

theorem subCm1_taint : Cert (sub3 aCm1 aC aOne) := ⟨_, by taint_decide⟩
end VG.Proof.Dsa.Arm.Prime
