module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Verified

/-! # DSA parameter generation on i686, for every SHA-1, SHA-256 and Miller–Rabin backend -/

@[expose] public section
namespace VG.Generic.Sha1.Sha256.MillerRabin.X86.Dsa
open VG VG.X86 VG.Proof.Dsa.X86.Generation VG.Proof.MillerRabin.X86

def artifacts (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    List Artifact :=
  let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
  [Spec.Dsa.generateParametersApi.artifact target {
    suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
    notes := ["The complete bounded parameter search runs in verified code: seed hashing, subgroup \
      construction, prime search, generator selection and output copying or zeroing, calling the \
      probable-prime tests of each size, the shared exponentiation and the domain check, each \
      verified separately. The three input tapes are public under the contract. Only 1024/160, \
      2048/256 and 3072/256 are generated."]
    code := Impl.Dsa.X86.Generation.code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)
    stack := 216
    consts := Impl.RsaKeyGen.TrialTable32.consts
    verified := verified v1 v256 v
    spSafe := code_all v1 v256 v
    features := hashes ++ v.features.filter (!hashes.contains ·) }]

end VG.Generic.Sha1.Sha256.MillerRabin.X86.Dsa
