module

public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.X86

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact X86.target {
    consts := Impl.Ed25519.X86.combConsts
    code := Impl.Ed25519.X86.scalarBase
    stack := 8
    verified := Proof.Ed25519.X86.scalarBase_verified }]
end VG.Artifacts.Ed25519ScalarBase.X86
