module

public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified
public import VerifiedGarbage.Proof.X25519.X86_64.Base.Ifma
public import VerifiedGarbage.Proof.X25519.X86_64.Base.Adx
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
public import VerifiedGarbage.Proof.X25519.X86_64.Base.Verified
public import VerifiedGarbage.Proof.X25519.X86_64.Verified
public import VerifiedGarbage.Proof.X25519.X86_64.Exchange
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.X25519.X86_64.Scrub
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit

/-! # X25519 (RFC 7748) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.X25519.X86_64

def artifacts : List Artifact := [
  Spec.X25519.exchangeApi.artifact X86_64.target
    { suffix := "_ifma"
      code := Impl.Xdh.X86_64.Fn.exchangeEvex "vg_x25519_ifma" Impl.X25519.X86_64.x25519Ifma 32
      verified := .scrubbed (Proof.X25519.X86_64.Scrub.exchangeIfma_scrubbed)
      spSafe := Proof.X25519.X86_64.Scrub.exchangeIfma_spSafe },
  Spec.X25519.exchangeApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.Xdh.X86_64.Fn.exchange "vg_x25519_adx" Impl.X25519.X86_64.x25519Adx 32
      verified := .scrubbed (Proof.X25519.X86_64.Scrub.exchangeAdx_scrubbed)
      spSafe := Proof.X25519.X86_64.Scrub.exchangeAdx_spSafe },
  Spec.X25519.exchangeApi.artifact X86_64.target
    { code := Impl.Xdh.X86_64.Fn.exchange "vg_x25519" Impl.X25519.X86_64.x25519 32
      verified := .scrubbed (Proof.X25519.X86_64.Scrub.exchange_scrubbed)
      spSafe := Proof.X25519.X86_64.Scrub.exchange_spSafe },
  Spec.X25519.x25519BaseApi.artifact X86_64.target
    { suffix := "_ifma"
      code := Impl.X25519.X86_64.Base.Fn.x25519BaseIfma
      verified := .scrubbed (Proof.X25519.X86_64.Scrub.baseIfma_scrubbed)
      spSafe := Proof.X25519.X86_64.Scrub.baseIfma_spSafe },
  Spec.X25519.x25519BaseApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.X25519.X86_64.Base.Fn.x25519BaseAdx
      verified := .scrubbed (Proof.X25519.X86_64.Scrub.baseAdx_scrubbed)
      spSafe := Proof.X25519.X86_64.Scrub.baseAdx_spSafe },
  Spec.X25519.x25519BaseApi.artifact X86_64.target
    { code := Impl.X25519.X86_64.Base.Fn.x25519Base
      verified := .scrubbed (Proof.X25519.X86_64.Scrub.base_scrubbed)
      spSafe := Proof.X25519.X86_64.Scrub.base_spSafe }]

end VG.Artifacts.X25519.X86_64
