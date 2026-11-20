module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Verified
public import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
public import VerifiedGarbage.Proof.X25519.AArch64.Base.Residue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.X25519.AArch64.Exchange
public import VerifiedGarbage.Proof.X25519.AArch64.ExchangeResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # X25519 (RFC 7748) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.X25519.AArch64

def artifacts : List Artifact := [
  Spec.X25519.exchangeApi.artifact AArch64.target {
    code := Proof.X25519.AArch64.ExchangeResidue.exchangeCode
    verified := .scrubbed Proof.X25519.AArch64.ExchangeResidue.exchangeCode_scrubbed },
  Spec.X25519.x25519BaseApi.artifact AArch64.target {
    written := [("scratch", 1024)]
    code := Proof.X25519.AArch64.Base.x25519BaseCleared
    verified := .scrubbed Proof.X25519.AArch64.Base.x25519BaseCleared_scrubbed
    writtenOk := Proof.X25519.AArch64.Base.x25519BaseCleared_written }]

end VG.Artifacts.X25519.AArch64
