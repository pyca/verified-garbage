module

import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCT
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowArithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCT
meta import VerifiedGarbage.Impl.Bignum.AArch64.WindowArithmetic
meta import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowArithmetic
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW RedcPreCtx)

theorem lazy_ct : RelCT isa (Two (Square.FinCtx 6))
    VG.Impl.Bignum.AArch64.WindowLazy.code (fun _ _ => True) :=
  two_taint _ (Square.pins_fin 6) (by taint_decide)

theorem reduce_ct (lazy : Bool) : RelCT isa (Two RedcPreCtx)
    (VG.Impl.Bignum.AArch64.WindowArithmetic.reduce 6 lazy) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.WindowArithmetic.reduce
  refine RelCT.seq (two_post BlockedRedc.redc_ct BlockedRedc.redc_ctx) ?_
  refine RelCT.seq (two_piece _ Square.pins_red (by taint_decide)
    (Square.finish_bases_ctx (by decide))) ?_
  cases lazy
  · exact FastFinish.finish_ct 6
  · exact lazy_ct

theorem square_ct : RelCT isa (Two FastW)
    (VG.Impl.Bignum.AArch64.WindowArithmetic.square 6) (fun _ _ => True) :=
  RelCT.seq WindowRaw.square_ct (reduce_ct true)

theorem product_ct : RelCT isa (Two FastW)
    (VG.Impl.Bignum.AArch64.WindowArithmetic.product 6 6 5) (fun _ _ => True) :=
  RelCT.seq WindowRaw.product_ct (reduce_ct false)

end VG.Proof.Bignum.AArch64.WindowArithmetic
