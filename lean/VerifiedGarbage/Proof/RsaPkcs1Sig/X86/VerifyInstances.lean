module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackSafety

/-! # Bind the verified baseline precomputed RSA operation -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86

def baseline : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name
  code := Impl.Bignum.X86.PrecomputedFn.code
  verified := VG.Proof.Bignum.X86.precomputed_verified
  stack := by decide +kernel
  noSp := NoSp.of_all (by decide +kernel)

end VG.Proof.RsaPkcs1Sig.X86.Ver
