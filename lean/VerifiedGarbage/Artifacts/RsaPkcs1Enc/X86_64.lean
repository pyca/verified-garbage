module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecHash
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
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndCT
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
public import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
public import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
public import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.Store
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64

/-! # RSAES-PKCS1-v1_5 decryption with implicit rejection on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.X86_64.MdHashRsaPrivateCrt

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

end VG.Artifacts.RsaPkcs1Enc.X86_64.MdHashRsaPrivateCrt

-- PKCS #1 v1.5 encryption over precomputed RSA public variants
namespace VG.Artifacts.RsaPkcs1Enc.X86_64.RsaPublicPrecomputed

open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.RsaPkcs1Enc.X86_64

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Enc.X86_64.Random.code (Rnd.encName v) (Rnd.encCode v)
    stack := Rnd.rndStack
    verified := Rnd.code_verified v
    spSafe := Rnd.code_spSafe v
    features := v.features }]

end VG.Artifacts.RsaPkcs1Enc.X86_64.RsaPublicPrecomputed

namespace VG.Artifacts.RsaPkcs1Enc.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.MdHash.X86_64.variants.flatMap fun v => VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap fun v2 => MdHashRsaPrivateCrt.artifacts v v2) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap fun v => RsaPublicPrecomputed.artifacts v)

end VG.Artifacts.RsaPkcs1Enc.X86_64
