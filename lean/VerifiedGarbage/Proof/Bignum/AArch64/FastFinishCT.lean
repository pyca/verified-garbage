module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
meta import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Proof.Bignum.AArch64

/-- Carries and selected values remain secret; addresses and counts depend
only on the public workspace layout. -/
theorem finish_ct (o : Nat) : RelCT isa (Two (Square.FinCtx o))
    VG.Impl.Bignum.AArch64.FastFinish.code (fun _ _ => True) :=
  two_taint _ (Square.pins_fin o) (by taint_decide)

end VG.Proof.Bignum.AArch64.FastFinish
