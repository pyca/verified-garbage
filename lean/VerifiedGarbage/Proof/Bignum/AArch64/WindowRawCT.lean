module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetupCT

import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCTRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Bignum.AArch64.WindowRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCTRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW RedcPreCtx)
open VG.Proof.Bignum.AArch64.ProductEight (SetupFast)

theorem triangle_ct : RelCT isa (Two FastW)
    (VG.Impl.Bignum.AArch64.WindowRaw.triangle 6) (Two (WindowSetup.DiagCtx 6)) := by
  unfold VG.Impl.Bignum.AArch64.WindowRaw.triangle
  refine RelCT.seq (two_piece _ ProductEight.pins_fast (by taint_decide)
    WindowSetup.start_ctx) ?_
  apply RelCT.assoc
  exact RelCT.seq (two_piece _ WindowSetup.pins_start (by taint_decide)
    (square_preparation_ctx (by decide)))
    (RelCT.seq (WindowSparse.rows_ct (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide))
      (two_piece _ (fun L s t hs ht => pins_goodW L s t hs.fast.1 ht.fast.1) (by taint_decide) (square_finish_ctx (by decide))))

theorem square_ct : RelCT isa (Two FastW)
    (VG.Impl.Bignum.AArch64.WindowRaw.square 6) (Two RedcPreCtx) :=
  RelCT.seq triangle_ct (two_piece _ (WindowSetup.pins_diagonal 6) (by taint_decide)
    (WindowSetup.diagonal_ctx (by decide) (by decide) (by decide)))

theorem product_ct : RelCT isa (Two FastW)
    (VG.Impl.Bignum.AArch64.WindowRaw.product 6 5) (Two RedcPreCtx) := by
  unfold VG.Impl.Bignum.AArch64.WindowRaw.product
  refine RelCT.seq (two_piece _ ProductEight.pins_fast (by taint_decide)
    WindowSetup.start_ctx) ?_
  apply RelCT.assoc
  exact RelCT.seq (two_piece _ WindowSetup.pins_start (by taint_decide)
    (preparation_ctx (b := 5) (by decide)))
    (RelCT.seq (ProductEight.rows_ct (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by taint_decide))
      (two_piece _ (ProductEight.pins_final 6 5) (by taint_decide) product_finish_ctx))

end VG.Proof.Bignum.AArch64.WindowRaw
