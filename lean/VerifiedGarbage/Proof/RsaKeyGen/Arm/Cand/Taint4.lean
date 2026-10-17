module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint0
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the taint analysis of trial division -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate

theorem trial_taint : Cert (seqs trial) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Cand
