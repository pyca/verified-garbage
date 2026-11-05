module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Widths
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.TCB.X86_64.Print

/-! # DSA parameter generation with every SHA-1, SHA-256 and Miller–Rabin backend on x86-64 -/

@[expose] public section
namespace VG.Generic.MdHash.MdHash.MillerRabin.X86_64.Dsa
open VG.Proof.Dsa.X86_64.Generation.Widths VG.Proof.MillerRabin.X86_64

def artifacts (v1 v256 : Proof.Pbkdf2.Md.X86_64.MdHash) (v : RoundImpl) : List Artifact :=
  if h1 : v1.mgf.G.rust = "sha1" then
    if h256 : v256.mgf.G.rust = "sha256" then
      let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
      [Spec.Dsa.generateParametersApi.artifact X86_64.target {
        suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
        stack := 600
        code := code v1 v256 v
        verified := code_verified v1 v256 v h1 h256
        spSafe := code_spSafe v1 v256 v
        features := hashes ++ v.features.filter (!hashes.contains ·) }]
    else []
  else []

end VG.Generic.MdHash.MdHash.MillerRabin.X86_64.Dsa
