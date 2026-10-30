module

public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseAdx
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! Complete unsigned scalar multiplication by the Ed25519 base point. -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.X86_64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact X86_64.target {
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline
    verified := Proof.Ed25519.X86_64.scalarBase_precomputed_verified
      (fld := Impl.X25519.X86_64.baseline)
    stack := 8 },
  Spec.Ed25519.scalarBaseApi.artifact X86_64.target {
    suffix := "_adx"
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.scalarBase_adx
    verified := Proof.Ed25519.X86_64.scalarBase_adx_verified
    features := ["avx", "avx2", "bmi2", "adx"]
    stack := 8 },
  Spec.Ed25519.scalarBaseApi.artifact X86_64.target {
    suffix := "_ifma"
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.scalarBase_ifma
    verified := Proof.Ed25519.X86_64.Ifma.scalarBase_ifma_verified
    features := ["avx", "avx2", "bmi2", "adx", "avx512f", "avx512ifma", "avx512vl"]
    stack := 8 }]

end VG.Artifacts.Ed25519ScalarBase.X86_64
