module

public import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.X86

def artifacts : List Artifact := [
  Spec.Ed25519.verifyApi.artifact X86.target {
    notes := ["Includes SHA-512 of R || A || message, challenge \
      reduction, and strict verification of the Ed25519 equation."]
    consts := Impl.Ed25519.X86.bConsts
    code := Impl.Ed25519.X86.VerifyMessage.code
    stack := 280
    verified := Proof.Ed25519.X86.VerifyMessage.verifyMessage_verified }]

end VG.Artifacts.Ed25519VerifyMessage.X86
