module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
import VerifiedGarbage.Proof.Ed25519.AArch64.KeyPair
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Sha512Compress.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Expanded
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Verified
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed25519 (RFC 8032) on AArch64 -/

-- Ed25519 key-pair derivation from the seed on AArch64, for each SHA-512 implementation
namespace VG.Artifacts.Ed25519.AArch64.KeyPair

/-- Key-pair derivation with the one-shot SHA-512 digest of `h`'s compression function,
calling `vg_ed25519_public_key_expanded`. -/
def artifactsFor (v : Proof.Sha512.AArch64.Compress) : List (Artifact AArch64.target) :=
  [
  Spec.Ed25519.keyPairApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Ed25519.AArch64.KeyPair.Fn.keyPair v.suffix v.code
    verified := Proof.Ed25519.AArch64.KeyPair.keyPair_scrubbed v }]

def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519.AArch64.KeyPair

-- Ed25519 signing from the seed's SHA-512 digest on AArch64, for each SHA-512 implementation
namespace VG.Artifacts.Ed25519.AArch64.SignExpanded

def artifactsFor (v : Proof.Sha512.AArch64.Compress) : List (Artifact AArch64.target) :=
  [
  Spec.Ed25519.signExpandedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Ed25519.AArch64.SignCached.Fn.signExpanded v.impl
    verified := Proof.Ed25519.AArch64.SignCached.signExpanded_scrubbed v }]

def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519.AArch64.SignExpanded

-- Ed25519 whole-message verification on AArch64, for each SHA-512 implementation
namespace VG.Artifacts.Ed25519.AArch64.VerifyMessage

def artifactsFor (v : Proof.Sha512.AArch64.Compress) : List (Artifact AArch64.target) :=
  [
    Spec.Ed25519.verifyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Ed25519.AArch64.VerifyMessage.Fn.verify v.impl
      verified := Proof.Ed25519.AArch64.VerifyMessage.verifyMessage_scrubbed v }]

def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.Sha512Compress.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519.AArch64.VerifyMessage

namespace VG.Artifacts.Ed25519.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  KeyPair.artifacts ++
  SignExpanded.artifacts ++
  VerifyMessage.artifacts

spec_apis artifacts

end VG.Artifacts.Ed25519.AArch64
