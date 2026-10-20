module

public import VerifiedGarbage.Proof.Bignum.X86.CrtVerified
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedVerified
public import VerifiedGarbage.Proof.Bignum.X86.PublicVerified
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
public import VerifiedGarbage.Proof.Rsa.X86.CvVerified
public import VerifiedGarbage.Proof.Rsa.X86.CvStackSafety
public import VerifiedGarbage.Proof.Rsa.X86.KcVerified
public import VerifiedGarbage.Proof.Rsa.X86.KcStackSafety
public import VerifiedGarbage.Proof.Rsa.X86.RvVerified
public import VerifiedGarbage.Proof.Rsa.X86.RvStackSafety
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Bignum.X86.CrtStackSafety

/-! Public and private CRT RSA on baseline i686. -/

@[expose] public section
namespace VG.Artifacts.Rsa.X86

def artifacts : List Artifact := [
  Spec.Rsa.recoverPrimesApi.artifact X86.target {
    code := Impl.Rsa.X86.Recover.code
    verified := Proof.Rsa.X86.Recover.verified
    spSafe := Proof.Rsa.X86.Recover.code_sp
    stack := 20 },
  Spec.Rsa.checkKeyApi.artifact X86.target {
    code := Impl.Rsa.X86.KeyCheck.code true
    verified := Proof.Rsa.X86.KeyCheck.verified true
    spSafe := Proof.Rsa.X86.KeyCheck.code_sp true
    stack := 20 },
  Spec.Rsa.checkCrtKeyApi.artifact X86.target {
    code := Impl.Rsa.X86.KeyCheck.code false
    verified := Proof.Rsa.X86.KeyCheck.verified false
    spSafe := Proof.Rsa.X86.KeyCheck.code_sp false
    stack := 20 },
  Spec.Rsa.crtValuesApi.artifact X86.target {
    code := Impl.Rsa.X86.CrtValues.code
    verified := Proof.Rsa.X86.CrtValues.verified
    spSafe := Proof.Rsa.X86.CrtValues.code_sp
    stack := 20 },
  Spec.Rsa.privateCrtApi.artifact X86.target {
    code := Impl.Bignum.X86.Crt.code
    verified := Proof.Bignum.X86.Crt.verified
    spSafe := Proof.Bignum.X86.Crt.code_sp
    stack := 20 },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86.target {
    notes := ["The exponent (at most 33 bits) is scanned from its low bit, branching on each \
      bit: a multiplication by the base for a set bit, a square of the base for every bit, and \
      the loop ends once no set bit is left (for `e = 65537`, 17 squares and 2 \
      multiplications)."]
    code := Impl.Bignum.X86.PrecomputedFn.code
    verified := Proof.Bignum.X86.precomputed_verified
    stack := 20 },
  Spec.Rsa.publicPrecomputeApi.artifact X86.target {
    code := Impl.Bignum.X86.PrecomputeFn.code
    verified := Proof.Bignum.X86.precompute_verified
    stack := 20 },
  Spec.Rsa.publicCheckedApi.artifact X86.target {
    notes := ["Public lengths select the limb width. Runtime-modulus Montgomery arithmetic \
      uses 32-bit limbs in the shared public scratch layout. The input acceptance mask is \
      applied after the exponentiation, which is `vg_rsa_public_precomputed_checked`'s: it \
      branches on each bit of the exponent and ends after its top bit. Callee-saved registers \
      reside in scratch."]
    code := Impl.Bignum.X86.PublicFn.code
    verified := Proof.Bignum.X86.public_verified
    stack := 20 }]

end VG.Artifacts.Rsa.X86
