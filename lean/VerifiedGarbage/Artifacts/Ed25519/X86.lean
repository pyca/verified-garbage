module

public import VerifiedGarbage.Proof.Ed25519.X86.KeyPair
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Verified
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Verified

/-! # Ed25519 (RFC 8032) on x86 -/

@[expose] public section

namespace VG.Artifacts.Ed25519.X86

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact X86.target {
    code := Impl.Ed25519.X86.KeyPair.keyPair Spec.Sha512.digest512Api.name
      Proof.Ed25519.X86.KeyPair.dgCode "vg_ed25519_public_key_expanded"
      Impl.Ed25519.X86.PublicKey.publicKeyExpanded
    stack := 628
    verified := Proof.Ed25519.X86.KeyPair.verified },
  Spec.Ed25519.signExpandedApi.artifact X86.target {
    code := Impl.Ed25519.X86.SignCached.codeExpanded
    stack := 280
    verified := Proof.Ed25519.X86.SignCached.signExpanded_verified },
  Spec.Ed25519.verifyApi.artifact X86.target {
    code := Impl.Ed25519.X86.VerifyMessage.code
    stack := 280
    verified := Proof.Ed25519.X86.VerifyMessage.verifyMessage_verified }]

end VG.Artifacts.Ed25519.X86
