module

public import VerifiedGarbage.Spec.Rsa.Contract

/-! # RSA: the working space of the public-key functions

The working space the private-key functions are given is enough for the
public-key functions they and the encryption and verification functions
call. -/

@[expose] public section

namespace VG.Proof.Rsa

/-- `scratchWords` words of working space are at least `publicScratchWords`
for every modulus length `lenValid` admits. -/
theorem publicScratch_le {k z : Nat} (hk : Spec.Rsa.lenValid k) (h : Spec.Rsa.scratchWords k ≤ z) :
    Spec.Rsa.publicScratchWords k ≤ z := by
  unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords
  unfold Spec.Rsa.scratchWords at h
  have := hk.1
  omega

end VG.Proof.Rsa
