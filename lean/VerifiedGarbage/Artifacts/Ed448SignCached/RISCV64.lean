module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignVerified
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
# Ed448 signing with a cached public key on RISC-V

The signature and documentation come from the reviewed Ed448 API. The
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448SignCached.RISCV64

def artifacts : List Artifact := [
  Spec.Ed448.signCachedApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.Whole.signCachedCode
    stack := 1696
    verified := Proof.Ed448.RISCV64.Whole.signCached_framed Proof.Ed448.baseLadder2_ok }]

end VG.Artifacts.Ed448SignCached.RISCV64
