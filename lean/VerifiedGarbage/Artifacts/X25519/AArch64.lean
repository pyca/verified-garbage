module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Verified
public import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X25519 (RFC 7748) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.X25519.AArch64

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact AArch64.target {
    code := Impl.X25519.AArch64.AltLadder.x25519
    verified := Proof.X25519.AArch64.AltLadder.x25519_verified },
  Spec.X25519.x25519BaseApi.artifact AArch64.target {
    consts := Impl.Ed25519.AArch64.combConsts
    written := [("scratch", 1024)]
    code := Impl.X25519.AArch64.Base.x25519Base
    verified := Proof.X25519.AArch64.Base.x25519Base_verified
    writtenOk := Proof.X25519.AArch64.Base.x25519Base_written }]

end VG.Artifacts.X25519.AArch64
