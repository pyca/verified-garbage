module

public import VerifiedGarbage.Proof.Sha3.AArch64.Variant

@[expose] public section
namespace VG.Proof.Sha3.AArch64

/-- The sponge, its contract and its call summaries do not depend on the
paired ML-DSA sampler choice. Its instruction requirements are added by the
ML-DSA registrations that use paired SHA3, independently of sponge features. -/
def withPairedSha3 (v : Permutation) : Permutation :=
  { v with callee := { v.callee with pairedSha3 := true } }

/-- Existing baseline and SHA3 backends already have their paired choices.
A further scalar backend needs its own hardware-paired companion too. -/
def mldsaModes (v : Permutation) : List Permutation :=
  if v.callee.suffix.isEmpty || v.callee.pairedSha3 then [v]
  else [v, withPairedSha3 v]

def mldsaFeatures (v : Permutation) : List String :=
  (v.features ++ if v.callee.pairedSha3 then ["sha3"] else []).eraseDups

end VG.Proof.Sha3.AArch64
