module

public import VerifiedGarbage.Proof.Bignum.X86.PublicVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Checked public RSA on baseline i686. -/

@[expose] public section
namespace VG.Artifacts.Rsa.X86

def artifacts : List Artifact := [
  Spec.Rsa.publicCheckedApi.artifact X86.target {
    notes := ["Public lengths select the limb width. Runtime-modulus Montgomery arithmetic \
      uses 32-bit limbs in the shared public scratch layout. The input acceptance mask is \
      applied after a fixed 64-step exponentiation. Callee-saved registers reside in scratch."]
    code := Impl.Bignum.X86.PublicFn.code
    verified := Proof.Bignum.X86.public_verified
    stack := 20 }]

end VG.Artifacts.Rsa.X86
