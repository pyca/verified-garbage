module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackSafety
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Verified

/-! # Bind the verified baseline precomputed RSA operation -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86

def baseline : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name
  code := Impl.Bignum.X86.PrecomputedRt.code
  verified := VG.Proof.Bignum.X86.PrecomputedRt.verified
  stack := by decide +kernel
  noSp := NoSp.of_all (by decide +kernel)

end VG.Proof.RsaPkcs1Sig.X86.Ver
