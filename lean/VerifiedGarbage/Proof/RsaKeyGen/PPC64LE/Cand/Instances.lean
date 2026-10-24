module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Verified
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.TrialOk

/-!
# `vg_rsa_keygen_candidate` on PPC64LE: verified

`candidate_verified`: `cand_verified` with the shared trial division
(`Trial.trial hTrial`, `trial_divOk`), for any implementation of the
Miller–Rabin round, which the registration
(`Generic/MillerRabin/PPC64LE/RsaKeyGen.lean`) takes from each variant.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

theorem candidate_verified (R : RoundImpl) :
    Verified target (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code
      (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial VG.Impl.RsaKeyGen.PPC64LE.Candidate.hTrial) R.name R.code) contract :=
  cand_verified TrialOk.trial_divOk R

end VG.Proof.RsaKeyGen.PPC64LE.Cand
