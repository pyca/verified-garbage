module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.Ed25519.AArch64.KeyPair
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Sha512Compress.AArch64
public import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Expanded
public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Verified

/-! # Ed25519 (RFC 8032) on AArch64 -/

@[expose] public section

-- Ed25519 key-pair derivation from the seed on AArch64, for each SHA-512 implementation
namespace VG.Artifacts.Ed25519.AArch64.KeyPair

/-- Key-pair derivation with the one-shot SHA-512 digest of `h`'s compression function,
calling `vg_ed25519_public_key_expanded`. -/
def artifactsFor (v : Proof.Sha512.AArch64.Compress) : List Artifact :=
  [
  Spec.Ed25519.keyPairApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Ed25519.AArch64.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ v.suffix)
      (Proof.Ed25519.AArch64.KeyPair.dgCode v) "vg_ed25519_public_key_expanded"
      Impl.Ed25519.AArch64.PublicKey.codeExpanded
    stack := 944
    verified := Proof.Ed25519.AArch64.KeyPair.verified v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519.AArch64.KeyPair

-- Ed25519 signing from the seed's SHA-512 digest on AArch64, for each SHA-512 implementation
namespace VG.Artifacts.Ed25519.AArch64.SignExpanded

def artifactsFor (v : Proof.Sha512.AArch64.Compress) : List Artifact :=
  [
  Spec.Ed25519.signExpandedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Ed25519.AArch64.SignCached.codeExpanded v.code v.suffix
    stack := 352
    verified := Proof.Ed25519.AArch64.SignCached.signExpanded_verified v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519.AArch64.SignExpanded

-- Ed25519 whole-message verification on AArch64, for each SHA-512 implementation
namespace VG.Artifacts.Ed25519.AArch64.VerifyMessage

def artifactsFor (v : Proof.Sha512.AArch64.Compress) : List Artifact :=
  [
    Spec.Ed25519.verifyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Ed25519.AArch64.VerifyMessage.code v.code v.suffix
      stack := 352
      verified := Proof.Ed25519.AArch64.VerifyMessage.verifyMessage_verified v
      features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519.AArch64.VerifyMessage

namespace VG.Artifacts.Ed25519.AArch64

def artifacts : List Artifact :=
  KeyPair.artifacts ++
  SignExpanded.artifacts ++
  VerifyMessage.artifacts

end VG.Artifacts.Ed25519.AArch64
