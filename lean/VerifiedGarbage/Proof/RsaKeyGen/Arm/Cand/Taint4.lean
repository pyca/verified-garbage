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

/-! # A candidate on ARMv7: the taint analysis of trial division -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

theorem trial_taint : Cert (seqs trial) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Cand
