module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCTBase
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCT
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64

/-! # RSAES-PKCS1-v1_5 decryption with implicit rejection on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.AArch64.MdHashRsaPrivateCrt

open VG.Proof.RsaPkcs1Enc.AArch64 (privOf dec_sat)
open VG.Proof.RsaPkcs1Enc.AArch64.Dec (HH decStack dec_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact :=
  match v.sha256 with
  | none => []
  | some h => [
    Spec.RsaPkcs1Enc.decryptApi.artifact AArch64.target {
      suffix := Emit.qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      code := Impl.RsaPkcs1Enc.AArch64.Decrypt.code (HH h) (privOf c).name (privOf c).code
      stack := decStack (privOf c)
      verified := dec_verified h (privOf c) (dec_sat c)
      features := h.features ++ c.features.filter (!h.features.contains ·) }]

end VG.Artifacts.RsaPkcs1Enc.AArch64.MdHashRsaPrivateCrt

-- PKCS #1 v1.5 encryption over precomputed RSA public variants on AArch64
namespace VG.Artifacts.RsaPkcs1Enc.AArch64.RsaPublicPrecomputed

open VG.Proof.Rsa.AArch64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc
open VG.Proof.RsaPkcs1Enc.AArch64 (Rnd.encName Rnd.encCode Rnd.rndStack Rnd.code_verified Rnd.sat)

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Enc.AArch64.Random.code (Rnd.encName (pdOf v)) (Rnd.encCode (pdOf v))
    stack := Rnd.rndStack (pdOf v).stack
    verified := Rnd.code_verified (pdOf v) Pc.sat Rnd.sat
    features := v.features }]

end VG.Artifacts.RsaPkcs1Enc.AArch64.RsaPublicPrecomputed

namespace VG.Artifacts.RsaPkcs1Enc.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.MdHash.AArch64.variants.flatMap fun v => VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap fun v2 => MdHashRsaPrivateCrt.artifacts v v2) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap fun v => RsaPublicPrecomputed.artifacts v)

end VG.Artifacts.RsaPkcs1Enc.AArch64
