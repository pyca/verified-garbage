module
public import VerifiedGarbage.Proof.Rsa.X86.BatchInstance

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Verified
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Verified
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
public import VerifiedGarbage.Proof.Rsa.X86.CvVerified
public import VerifiedGarbage.Proof.Rsa.X86.KcVerified
public import VerifiedGarbage.Proof.Rsa.X86.RvVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.X86.RtShape

/-! Public and private CRT RSA on baseline i686. -/

@[expose] public section
namespace VG.Artifacts.Rsa.X86

def artifacts : List Artifact := [
  Spec.Rsa.recoverPrimesApi.artifact X86.target {
    notes := ["The modulus's length gives the numbers' width at run time; every Montgomery \
      multiplication calls `vg_rsa_mont_mul_at`. At 2048 bits and above a fixed-width binary pass \
      fuses exponentiation and root search; smaller moduli use the windowed schedule. The public \
      candidate index selects repeated addition or a bounded seven-bit multiplication. The search \
      ends after the attempt that recovers the factors, so the attempt count is public. GCDs at \
      2048/3072/4096 bits apply matrices of thirty divsteps per full-width update. Private \
      values select no branch. Callee-saved registers reside in scratch."]
    code := Impl.Rsa.X86.RecoverRt.code
    verified := Proof.Rsa.X86.Recover.verified
    spSafe := Proof.Rsa.X86.RtShape.recover_spSafe
    stack := 40 },
  Spec.Rsa.checkKeyApi.artifact X86.target {
    notes := ["The modulus's length gives the numbers' width at run time: every operation computes \
      its arrays' addresses from it. The length is public; only the checks of the modulus and the public \
      exponent select a branch. Callee-saved registers reside in scratch."]
    code := Impl.Rsa.X86.KeyCheckRt.code true
    verified := Proof.Rsa.X86.KeyCheck.verified true
    spSafe := Proof.Rsa.X86.RtShape.check_spSafe true
    stack := 20 },
  Spec.Rsa.checkCrtKeyApi.artifact X86.target {
    notes := ["The modulus's length gives the numbers' width at run time: every operation computes \
      its arrays' addresses from it. The length is public; only the checks of the modulus and the public \
      exponent select a branch. Callee-saved registers reside in scratch."]
    code := Impl.Rsa.X86.KeyCheckRt.code false
    verified := Proof.Rsa.X86.KeyCheck.verified false
    spSafe := Proof.Rsa.X86.RtShape.check_spSafe false
    stack := 20 },
  Spec.Rsa.crtValuesApi.artifact X86.target {
    notes := ["The modulus and prime lengths are public. Balanced 2048/3072/4096-bit keys use \
      thirty-step batched inversion at the prime width; other lengths use the general inverse. \
      Each batch updates signed GCD rows and Montgomery-reduced coefficient rows. Private values \
      select no branch. Callee-saved registers reside in scratch."]
    code := Impl.Rsa.X86.CrtValuesRt.code
    verified := Proof.Rsa.X86.CrtValues.verified
    spSafe := Proof.Rsa.X86.RtShape.crtValues_spSafe
    stack := 20 },
  Spec.Rsa.privateCrtApi.artifact X86.target {
    notes := ["The modulus's length gives the numbers' width at run time; every Montgomery \
      multiplication calls `vg_rsa_mont_mul_at`. Each factor whose length (`p_len`, `q_len`) fits half \
      the modulus's width has the input reduced modulo it at the modulus's width, then its windowed \
      exponentiation at half the width; a longer factor's runs at the modulus's width. The lengths \
      are public; the factors' values select no branch. Callee-saved registers reside in scratch."]
    code := Impl.Bignum.X86.CrtRt.code
    verified := Proof.Bignum.X86.CrtRt.verified
    spSafe := Proof.Rsa.X86.RtShape.privateCrt_spSafe
    stack := 40 },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86.target {
    notes := ["The modulus's length gives the numbers' width at run time; every Montgomery \
      multiplication calls `vg_rsa_mont_mul_at`. The exponentiation branches on each bit of the \
      public exponent, multiplying by the base only for a set bit, and ends after its top bit; \
      the input acceptance mask is applied after it. Callee-saved registers reside in scratch."]
    code := Impl.Bignum.X86.PrecomputedRt.code
    verified := Proof.Bignum.X86.PrecomputedRt.verified
    spSafe := Proof.Rsa.X86.RtShape.precomputed_spSafe
    stack := 40 },
  Spec.Rsa.publicPrecomputeApi.artifact X86.target {
    code := Impl.Bignum.X86.PrecomputeFn.code
    verified := Proof.Bignum.X86.precompute_verified
    stack := 20 },
  Spec.Rsa.publicCheckedApi.artifact X86.target {
    notes := ["The modulus's length gives the numbers' width at run time; every Montgomery \
      multiplication calls `vg_rsa_mont_mul_at`. The exponentiation branches on each bit of the \
      public exponent, multiplying by the base only for a set bit, and ends after its top bit; \
      the input acceptance mask is applied after it. Callee-saved registers reside in scratch."]
    code := Impl.Bignum.X86.PublicRt.code
    verified := Proof.Bignum.X86.PublicRt.verified
    spSafe := Proof.Rsa.X86.RtShape.public_spSafe
    stack := 40 }]

end VG.Artifacts.Rsa.X86
