module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendCorrect

/-! # Parameter generation with every supported SHA-1, SHA-256, and Miller–Rabin backend -/

@[expose] public section
namespace VG.Generic.MdHash.MdHash.MillerRabin.X86_64.Dsa

open VG.Proof.Dsa.X86_64.Generation VG.Proof.MillerRabin.X86_64

def artifacts (v1 v256 : Proof.Pbkdf2.Md.X86_64.MdHash) (v : RoundImpl) : List Artifact :=
  if h1 : v1.mgf.G.rust = "sha1" then
    if h256 : v256.mgf.G.rust = "sha256" then
      let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
      [Spec.Dsa.generateParametersApi.artifact X86_64.target {
        suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
        stack := 472
        notes := ["The complete bounded parameter search runs in verified code: seed hashing, \
          subgroup construction, prime search, shared windowed Miller–Rabin tests, generator \
          selection, domain validation, and output copying or zeroing. The three input tapes \
          are public under the contract. Only 1024/160, 2048/256, and 3072/256 are generated."]
        code := Impl.Dsa.X86_64.Generation.code v1.H.stream v256.H.stream v.mont.toS.mm v.mont.mm (Kernel.called v).run
        verified := backend_verified v1 v256 v h1 h256
        spSafe := (backend_safe v1 v256 v).sp
        features := hashes ++ v.features.filter (!hashes.contains ·) }]
    else []
  else []

end VG.Generic.MdHash.MdHash.MillerRabin.X86_64.Dsa
