module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Base.Ifma
import VerifiedGarbage.Proof.X25519.X86_64.Base.Adx
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Base.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Exchange
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
import VerifiedGarbage.Proof.X25519.X86_64.Scrub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X25519 (RFC 7748) on x86-64 -/

namespace VG.Artifacts.X25519.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.X25519.exchangeApi.artifact X86_64.target
    { suffix := "_ifma"
      code := Impl.Xdh.X86_64.Fn.exchangeEvex "vg_x25519_ifma" Impl.X25519.X86_64.x25519Ifma 32
      verified := Proof.X25519.X86_64.Scrub.exchangeIfma_scrubbed
      spSafe := Proof.X25519.X86_64.Scrub.exchangeIfma_spSafe },
  Spec.X25519.exchangeApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.Xdh.X86_64.Fn.exchange "vg_x25519_adx" Impl.X25519.X86_64.x25519Adx 32
      verified := Proof.X25519.X86_64.Scrub.exchangeAdx_scrubbed
      spSafe := Proof.X25519.X86_64.Scrub.exchangeAdx_spSafe },
  Spec.X25519.exchangeApi.artifact X86_64.target
    { code := Impl.Xdh.X86_64.Fn.exchange "vg_x25519" Impl.X25519.X86_64.x25519 32
      verified := Proof.X25519.X86_64.Scrub.exchange_scrubbed
      spSafe := Proof.X25519.X86_64.Scrub.exchange_spSafe },
  Spec.X25519.x25519BaseApi.artifact X86_64.target
    { suffix := "_ifma"
      code := Impl.X25519.X86_64.Base.Fn.x25519BaseIfma
      verified := Proof.X25519.X86_64.Scrub.baseIfma_scrubbed
      spSafe := Proof.X25519.X86_64.Scrub.baseIfma_spSafe },
  Spec.X25519.x25519BaseApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.X25519.X86_64.Base.Fn.x25519BaseAdx
      verified := Proof.X25519.X86_64.Scrub.baseAdx_scrubbed
      spSafe := Proof.X25519.X86_64.Scrub.baseAdx_spSafe },
  Spec.X25519.x25519BaseApi.artifact X86_64.target
    { code := Impl.X25519.X86_64.Base.Fn.x25519Base
      verified := Proof.X25519.X86_64.Scrub.base_scrubbed
      spSafe := Proof.X25519.X86_64.Scrub.base_spSafe }]

spec_apis artifacts

end VG.Artifacts.X25519.X86_64
