module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncPre
public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncVerified
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkVerified
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkPre
import VerifiedGarbage.Proof.RsaPss.AArch64.Depth
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCVerified
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCVerified

/-!
# RSASSA-PSS on AArch64, for each hash function and RSA implementation

For each hash function `v` (a variant of `MdHash`), `encode` and
`checkEncoding` as callees (`encOf`, `chkOf`), which
`Generic/MdHash/AArch64/RsaPss.lean` registers; and the proofs of signing
and of verification with cached public-key values calling them and an
implementation `c` of the RSA operation, which
`Generic/MdHash/RsaPrivateCrt/AArch64/RsaPss.lean` and
`Generic/MdHash/RsaPublicPrecomputed/AArch64/RsaPss.lean` register.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf pdOf)

/-- `encode` made with `v`'s compression function. -/
def encOf (v : Proof.Pbkdf2.Md.AArch64.MdHash) : EncImpl v.mgf.G where
  name := s!"vg_rsa_pss_{v.mgf.G.rust}_mgf1_{v.mgf.G.rust}_encode" ++ v.suffix
  code := Impl.RsaPss.AArch64.encode v.H
  stack := Enc.encStack
  verified := Enc.code_verified v.ok v.mgf.hash v.mgf.len (Enc.mgf_valid v.mgf) v.pss (Enc.enc_sat v.mgf.mem)
  depth := by have := encode_depth v.ok; unfold Enc.encStack Sgn.stk Impl.RsaPss.AArch64.frameBytes; omega
  pos := by decide
  le := by decide
  suffix := v.suffix
  features := v.features

/-- `checkEncoding` made with `v`'s compression function. -/
def chkOf (v : Proof.Pbkdf2.Md.AArch64.MdHash) : ChkImpl v.mgf.G where
  name := s!"vg_rsa_pss_{v.mgf.G.rust}_mgf1_{v.mgf.G.rust}_check_encoding" ++ v.suffix
  code := Impl.RsaPss.AArch64.checkEncoding v.H
  stack := Chk.chkStack
  verified := Chk.code_verified v.ok v.mgf.hash v.mgf.len (Enc.mgf_valid v.mgf) v.pss (Chk.chk_sat v.mgf.mem)
  depth := by have := chk_depth v.ok; unfold Chk.chkStack Sgn.stk Impl.RsaPss.AArch64.frameBytes; omega
  pos := by decide
  le := by decide
  suffix := v.suffix
  features := v.features

theorem sign_verified (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target
      (Impl.RsaPss.AArch64.signC (encOf v).name (encOf v).code (privOf c).name (privOf c).code)
      (Spec.RsaPss.signContract v.mgf.G v.mgf.G AArch64.abi (Sgn.stk (privOf c).stack)) :=
  Sgn.code_verified (encOf v) (privOf c) (show Enc.encStack ≤ Proof.Rsa.AArch64.stackBytes by decide) (Nat.le_refl _)
    (Sgn.sign_sat v.mgf.mem)

theorem verify_verified (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl) :
    Verified AArch64.target
      (Impl.RsaPss.AArch64.verifyC (chkOf v).name (chkOf v).code (pdOf c).name (pdOf c).code)
      (Spec.RsaPss.verifyPrecomputedContract v.mgf.G v.mgf.G AArch64.abi (Sgn.stk 352)) :=
  Vfy.code_verified (pdOf c) (chkOf v) (show 16 ≤ 352 by decide) (show Chk.chkStack ≤ 352 by decide) (Vfy.verify_sat v.mgf.mem)

end VG.Proof.RsaPss.AArch64
