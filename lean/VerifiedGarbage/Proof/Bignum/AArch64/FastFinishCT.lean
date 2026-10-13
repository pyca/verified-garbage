module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
meta import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Proof.Bignum.AArch64

/-- Carries and selected values remain secret; addresses and counts depend
only on the public workspace layout. -/
theorem finish_ct (o : Nat) : RelCT isa (Two (Square.FinCtx o))
    VG.Impl.Bignum.AArch64.FastFinish.code (fun _ _ => True) :=
  two_taint _ (Square.pins_fin o) (by taint_decide)

end VG.Proof.Bignum.AArch64.FastFinish
