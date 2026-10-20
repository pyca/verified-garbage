module

public import VerifiedGarbage.Proof.Bignum.X86.CrtStackSafety
public import VerifiedGarbage.Proof.Bignum.X86.CrtVerified
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedVerified
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Verified
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
public import VerifiedGarbage.Proof.Rsa.X86.CvVerified
public import VerifiedGarbage.Proof.Rsa.X86.CvStackSafety
public import VerifiedGarbage.Proof.Rsa.X86.KcVerified
public import VerifiedGarbage.Proof.Rsa.X86.KcStackSafety
public import VerifiedGarbage.Proof.Rsa.X86.RvVerified
public import VerifiedGarbage.Proof.Rsa.X86.RvStackSafety
public import VerifiedGarbage.Proof.Framework.Registration

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
    notes := ["Each factor whose length (`p_len`, `q_len`) fits half the modulus's words has the \
      input reduced modulo it at the modulus's width, then its exponentiation at half the width, \
      with half the exponent's bits: a balanced key's. A longer factor's exponentiation runs at the \
      modulus's width. The lengths are public; the factors' values select no branch."]
    code := Impl.Bignum.X86.Crt.code
    verified := Proof.Bignum.X86.Crt.verified
    spSafe := Proof.Bignum.X86.Crt.code_sp
    stack := 40 },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86.target {
    code := Impl.Bignum.X86.PrecomputedFn.code
    verified := Proof.Bignum.X86.precomputed_verified
    stack := 20 },
  Spec.Rsa.publicPrecomputeApi.artifact X86.target {
    code := Impl.Bignum.X86.PrecomputeFn.code
    verified := Proof.Bignum.X86.precompute_verified
    stack := 20 },
  Spec.Rsa.publicCheckedApi.artifact X86.target {
    notes := ["The modulus's length gives the numbers' width at run time; every Montgomery \
      multiplication calls `vg_rsa_mont_mul`. The input acceptance mask is applied after a fixed \
      64-step exponentiation. Callee-saved registers reside in scratch."]
    code := Impl.Bignum.X86.PublicRt.code
    verified := Proof.Bignum.X86.PublicRt.verified
    stack := 40 }]

end VG.Artifacts.Rsa.X86
