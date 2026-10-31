module

public import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecHash
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT2
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT3
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecResult
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncEM
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Octets
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT2
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT3
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecResult
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncEM
import VerifiedGarbage.Proof.RsaPkcs1Sig.Octets

/-! # RSAES-PKCS1-v1_5 decryption with implicit rejection on x86-64 -/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPkcs1Enc

open VG.Proof.RsaPkcs1Enc.X86_64 (privOf decStack)
open VG.Proof.RsaPkcs1Enc.X86_64.Dec (HH dec_verified dec_spSafe)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact :=
  match v.sha256 with
  | none => []
  | some h => [
    Spec.RsaPkcs1Enc.decryptApi.artifact X86_64.target {
      suffix := Emit.qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      code := Impl.RsaPkcs1Enc.X86_64.Decrypt.code (HH h) (privOf c).name (privOf c).code
      stack := decStack
      verified := dec_verified h (privOf c)
      spSafe := dec_spSafe h (privOf c)
      features := h.features ++ c.features.filter (!h.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.X86_64.RsaPkcs1Enc
