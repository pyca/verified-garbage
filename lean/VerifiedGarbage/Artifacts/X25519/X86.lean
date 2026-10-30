module

public import VerifiedGarbage.Proof.X25519.X86.Verified
import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Proof.X25519.X86.Base.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X25519.X86.Base.Lit

/-! # X25519 (RFC 7748) on x86 -/

@[expose] public section

namespace VG.Artifacts.X25519.X86

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact X86.target {
    code := Impl.X25519.X86.x25519
    stack := 8
    verified := Proof.X25519.X86.x25519_verified },
  Spec.X25519.x25519BaseApi.artifact X86.target {
    consts := Impl.Ed25519.X86.combConsts
    code := Impl.X25519.X86.Base.x25519Base
    stack := 8
    verified := Proof.X25519.X86.Base.x25519Base_verified }]

end VG.Artifacts.X25519.X86
