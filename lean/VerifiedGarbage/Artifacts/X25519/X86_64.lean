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
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit

/-! # X25519 (RFC 7748) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.X25519.X86_64

def artifacts : List Artifact := [
  Spec.X25519.exchangeApi.artifact X86_64.target {
    suffix := "_ifma"
    code := Impl.Xdh.X86_64.exchange "vg_x25519_ifma" Impl.X25519.X86_64.x25519Ifma 32
    stack := 24
    verified := Proof.X25519.X86_64.Exchange.exchange_ifma
    features := ["avx", "avx2", "bmi2", "adx", "avx512f", "avx512ifma", "avx512vl"] },
  Spec.X25519.exchangeApi.artifact X86_64.target {
    suffix := "_adx"
    code := Impl.Xdh.X86_64.exchange "vg_x25519_adx" Impl.X25519.X86_64.x25519Adx 32
    stack := 24
    verified := Proof.X25519.X86_64.Exchange.exchange_adx
    features := ["bmi2", "adx"] },
  Spec.X25519.exchangeApi.artifact X86_64.target {
    code := Impl.Xdh.X86_64.exchange "vg_x25519" Impl.X25519.X86_64.x25519 32
    stack := 24
    verified := Proof.X25519.X86_64.Exchange.exchange_baseline },
  Spec.X25519.x25519BaseApi.artifact X86_64.target {
    suffix := "_ifma"
    code := Impl.X25519.X86_64.Base.x25519BaseIfma
    stack := 8
    verified := Proof.X25519.X86_64.Base.x25519BaseIfma_verified
    features := ["avx", "avx2", "bmi2", "adx", "avx512f", "avx512ifma", "avx512vl"] },
  Spec.X25519.x25519BaseApi.artifact X86_64.target {
    suffix := "_adx"
    code := Impl.X25519.X86_64.Base.x25519BaseAdx
    stack := 8
    verified := Proof.X25519.X86_64.Base.x25519BaseAdx_verified
    features := ["avx", "avx2", "bmi2", "adx"] },
  Spec.X25519.x25519BaseApi.artifact X86_64.target {
    code := Impl.X25519.X86_64.Base.x25519Base Impl.X25519.X86_64.baseline
    stack := 8
    verified := Proof.X25519.X86_64.Base.x25519Base_verified }]

end VG.Artifacts.X25519.X86_64
