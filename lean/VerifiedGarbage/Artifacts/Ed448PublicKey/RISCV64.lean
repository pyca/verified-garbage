module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 public-key derivation on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed448PublicKey.RISCV64

def artifacts : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Whole.publicKeyCode
    stack := 1328
    verified := Proof.Ed448.RISCV64.Whole.publicKey_framed Proof.Ed448.baseLadder2_ok }]

end VG.Artifacts.Ed448PublicKey.RISCV64
