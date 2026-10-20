module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
meta import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Impl.Bignum.AArch64
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Proof.Bignum.AArch64

/-- Carries and selected values remain secret; addresses and counts depend
only on the public workspace layout. -/
theorem finish_ct (o : Nat) : RelCT isa (Two (Square.FinCtx o))
    VG.Impl.Bignum.AArch64.FastFinish.code (fun _ _ => True) :=
  two_taint _ (Square.pins_fin o) (by taint_decide)

end VG.Proof.Bignum.AArch64.FastFinish
