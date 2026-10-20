module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.RsaPss.AArch64.SignVerified
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre

/-!
# RSASSA-PSS on AArch64, for each hash function and RSA implementation

The proofs of signing and of verification with cached public-key values,
made with a hash function `v` (with MGF1 over the same hash function) and an
implementation `c` of the RSA operation, which
`Generic/MdHash/RsaPrivateCrt/AArch64/RsaPss.lean` and
`Generic/MdHash/RsaPublicPrecomputed/AArch64/RsaPss.lean` register.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf pdOf)

theorem sign_verified (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaPss.AArch64.sign v.H (privOf c).name (privOf c).code)
      (Spec.RsaPss.signContract v.mgf.G v.mgf.G AArch64.abi (Sgn.stk (privOf c).stack)) :=
  Sgn.code_verified v.ok v.mgf.hash v.mgf.len (Vfy.mgf_valid v.mgf) v.pss (privOf c)
    (show 16 ≤ Proof.Rsa.AArch64.stackBytes by decide) (Sgn.sign_sat v.mgf.mem)

theorem verify_verified (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl) :
    Verified AArch64.target (Impl.RsaPss.AArch64.verifyPrecomputed v.H (pdOf c).name (pdOf c).code)
      (Spec.RsaPss.verifyPrecomputedContract v.mgf.G v.mgf.G AArch64.abi (Sgn.stk 16)) :=
  Vfy.code_verified v.ok v.mgf.hash v.mgf.len (Vfy.mgf_valid v.mgf) v.pss (pdOf c) (by decide)
    (Nat.le_refl _) (Vfy.verify_sat v.mgf.mem)

end VG.Proof.RsaPss.AArch64
