module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # DSA parameter generation over refillable tapes with every SHA-1, SHA-256 and Miller–Rabin backend on AArch64 -/

@[expose] public section
namespace VG.Generic.MdHash.MdHash.MillerRabin.AArch64.Dsa

open VG.Proof.Dsa.AArch64.Generation VG.Proof.MillerRabin.AArch64

/-- DSA's parameter search for a SHA-1 and a SHA-256 backend for the same
CPUs (both baselines or both SHA-2 extensions), with each Miller–Rabin
round: either other pair needs the features of one of these, which runs
both hashes with them. -/
def artifacts (v1 v256 : Proof.Pbkdf2.Md.AArch64.MdHash) (v : RoundImpl) : List Artifact :=
  if v1.suffix != v256.suffix then [] else
  if h1 : v1.mgf.G.rust = "sha1" then
    if h256 : v256.mgf.G.rust = "sha256" then
      let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
      [Spec.Dsa.parameterSearchApi.artifact AArch64.target {
        suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
        stack := 768
        code := Impl.Dsa.AArch64.Generation.code v1.H v256.H (Proof.Dsa.AArch64.Generator.generatorStage v).run
          (Proof.Dsa.AArch64.ProbablePrime.primeTest v).run
        verified := Refill.backend_verified v1 v256 v h1 h256
        features := hashes ++ v.features.filter (!hashes.contains ·) }]
    else []
  else []

end VG.Generic.MdHash.MdHash.MillerRabin.AArch64.Dsa
