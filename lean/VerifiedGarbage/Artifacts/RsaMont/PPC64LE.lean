module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication in the RSA working space on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaMont.PPC64LE

def artifacts : List Artifact := [
  Spec.Rsa.Mont.mulApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 112 .r8 Impl.Bignum.PPC64LE.mul
    stack := 112
    verified := Proof.Bignum.PPC64LE.mul_verified }]

end VG.Artifacts.RsaMont.PPC64LE
