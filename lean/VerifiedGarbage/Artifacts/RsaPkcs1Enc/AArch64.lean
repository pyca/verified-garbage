module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCTBase
public import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64
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
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.AArch64.Sha256RsaPrivateCrt

open VG.Proof.RsaPkcs1Enc.AArch64 (privOf dec_sat privPOf decP_sat')
open VG.Proof.RsaPkcs1Enc.AArch64.Dec (HH decStack dec_verified decStackP decP_verified)

def artifacts (h : Proof.Sha256.AArch64.Compress) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact :=
  [
    Spec.RsaPkcs1Enc.decryptApi.artifact AArch64.target {
      suffix := qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      code := Impl.RsaPkcs1Enc.AArch64.Decrypt.code (HH h) (privOf c).name (privOf c).code
      stack := decStack (privOf c)
      verified := dec_verified h (privOf c) (dec_sat c) },
    Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact AArch64.target {
      suffix := qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      code := Impl.RsaPkcs1Enc.AArch64.Decrypt.codeP (HH h) (privPOf c).name (privPOf c).code
      stack := decStackP (privPOf c)
      verified := decP_verified h (privPOf c) (decP_sat' c) }]

end VG.Artifacts.RsaPkcs1Enc.AArch64.Sha256RsaPrivateCrt

namespace VG.Artifacts.RsaPkcs1Enc.AArch64

open VG.Proof.Rsa.AArch64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc
open VG.Proof.RsaPkcs1Enc.AArch64 (Rnd.encName Rnd.encCode Rnd.rndStack Rnd.code_verified Rnd.sat)

def artifacts : List Artifact :=
  (VG.Proof.Variants.Sha256Compress.AArch64.variants.flatMap fun v => VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap fun v2 => Sha256RsaPrivateCrt.artifacts v v2) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap fun (v : PublicImpl) => [
    Spec.RsaPkcs1Enc.encryptRandomApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Enc.AArch64.Random.code (Rnd.encName (pdOf v)) (Rnd.encCode (pdOf v))
      stack := Rnd.rndStack (pdOf v).stack
      verified := Rnd.code_verified (pdOf v) Pc.sat Rnd.sat }])

end VG.Artifacts.RsaPkcs1Enc.AArch64
