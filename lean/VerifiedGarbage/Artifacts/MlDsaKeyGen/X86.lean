module

public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # ML-DSA (FIPS 204) key generation on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.MlDsaKeyGen.X86

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact X86.target {
    code := Impl.MlDsa.X86.KeyGen.keyGen44
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact X86.target {
    code := Impl.MlDsa.X86.KeyGen.keyGen65
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact X86.target {
    code := Impl.MlDsa.X86.KeyGen.keyGen87
    stack := 96
    verified := Proof.MlDsa.X86.KeyGen.keyGen87_verified }]

end VG.Artifacts.MlDsaKeyGen.X86
