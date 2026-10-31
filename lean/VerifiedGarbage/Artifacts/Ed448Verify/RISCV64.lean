module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 verification on RISC-V

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.RISCV64

def artifacts : List Artifact := [
  Spec.Ed448.verifyApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Whole.verifyCode
    stack := 1616
    verified := Proof.Ed448.RISCV64.Whole.verify_framed Proof.Ed448.recover_ok Proof.Ed448.verifyEq4_ok }]

end VG.Artifacts.Ed448Verify.RISCV64
