module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.TCB.X86_64.Print

/-! # DSA parameter generation over refillable tapes with every SHA-1, SHA-256 and Miller–Rabin backend on x86-64 -/

@[expose] public section
namespace VG.Generic.MdHash.MdHash.MillerRabin.X86_64.Dsa
open VG.Proof.Dsa.X86_64.Generation.RefillBackend VG.Proof.MillerRabin.X86_64

/-- DSA's parameter search for a SHA-1 and a SHA-256 backend for the same
CPUs (both baselines, both SHA extensions, or SHA-1's AVX and BMI code with
SHA-256's AVX2 code, BMI2 coming only with AVX2), with each Miller–Rabin
round: any other pair needs the features of one of these, which runs both
hashes with them. -/
def artifacts (v1 v256 : Proof.Pbkdf2.Md.X86_64.MdHash) (v : RoundImpl) : List Artifact :=
  if !(v1.suffix == v256.suffix || (v1.suffix == "_avx_bmi" && v256.suffix == "_avx2")) then [] else
  if h1 : v1.mgf.G.rust = "sha1" then
    if h256 : v256.mgf.G.rust = "sha256" then
      let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
      [Spec.Dsa.parameterSearchApi.artifact X86_64.target {
        suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
        stack := 632
        code := searchCode v1 v256 v
        verified := search_verified v1 v256 v h1 h256
        spSafe := searchCode_spSafe v1 v256 v
        features := hashes ++ v.features.filter (!hashes.contains ·) }]
    else []
  else []

end VG.Generic.MdHash.MdHash.MillerRabin.X86_64.Dsa
