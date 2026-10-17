module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0

/-! # A candidate on ARMv7: the taint analysis of trial division -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

theorem trial_taint : Cert (seqs trial) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Cand
