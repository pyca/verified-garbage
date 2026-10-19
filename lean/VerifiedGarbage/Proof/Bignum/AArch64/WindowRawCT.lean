module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetupCT

import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCTRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHead
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHoles
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseRows
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTail
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTile
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Impl.Bignum.AArch64
meta import VerifiedGarbage.Impl.Bignum.AArch64.WindowRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCTRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHoles
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTail
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTile
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
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
