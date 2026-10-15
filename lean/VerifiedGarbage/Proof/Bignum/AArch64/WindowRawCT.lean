module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawCtContext
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW RedcPreCtx)
open VG.Proof.Bignum.AArch64.ProductEight (SetupFast)

theorem triangle_ct : RelCT isa (Two FastW)
    (VG.Impl.Bignum.AArch64.WindowRaw.triangle 6) (Two (SetupFast 6)) := by
  unfold VG.Impl.Bignum.AArch64.WindowRaw.triangle
  refine RelCT.seq (two_piece _ ProductEight.pins_fast (by taint_decide)
    (ProductEight.setup_fast_ctx (by decide))) ?_
  apply RelCT.assoc
  exact RelCT.seq (two_piece _ (ProductEight.pins_setup 6) (by taint_decide)
    (square_preparation_ctx (by decide)))
    (RelCT.seq (SquareEight.rows_ct (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide))
      (two_piece _ (SquareEight.pins_final 6) (by taint_decide) (square_finish_ctx (by decide))))

theorem square_ct : RelCT isa (Two FastW)
    (VG.Impl.Bignum.AArch64.WindowRaw.square 6) (Two RedcPreCtx) :=
  RelCT.seq triangle_ct (two_piece _ (SquareEight.pins_diagonal 6) (by taint_decide)
    (SquareEight.diagonal_ctx (by decide) (by decide) (by decide)))

theorem product_ct : RelCT isa (Two FastW)
    (VG.Impl.Bignum.AArch64.WindowRaw.product 6 5) (Two RedcPreCtx) := by
  unfold VG.Impl.Bignum.AArch64.WindowRaw.product
  refine RelCT.seq (two_piece _ ProductEight.pins_fast (by taint_decide)
    (ProductEight.setup_fast_ctx (by decide))) ?_
  apply RelCT.assoc
  exact RelCT.seq (two_piece _ (ProductEight.pins_setup 6) (by taint_decide)
    (preparation_ctx (b := 5) (by decide)))
    (RelCT.seq (ProductEight.rows_ct (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by taint_decide))
      (two_piece _ (ProductEight.pins_final 6 5) (by taint_decide) (product_finish_ctx (by decide))))

end VG.Proof.Bignum.AArch64.WindowRaw
