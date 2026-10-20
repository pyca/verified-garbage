module
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtHead

import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks RedcPreCtx)
open VG.Proof.Bignum.AArch64.ProductEight (SetupFast preparation finishRaw)

theorem pins_final (a : Nat) : Pins (fun L s => LoopCtx a L (blocks L) s) [.x0] :=
  fun L s t hs ht => pins_goodW L s t hs.fast.1 ht.fast.1

theorem pins_diagonal (a : Nat) : Pins (SetupFast a) [.x8, .x9, .x12] := by
  intro L s t hs ht r hr
  exact Square.pins_setup a L s t hs.1 ht.1 r
    ((show ∀ r ∈ [.x8, .x9, .x12], r ∈ [.x0, .x8, .x9, .x10, .x12, .x7] by decide) r hr)

/-- All square addresses and loop counts depend only on public workspace
layout. Products, operands, and arithmetic carries remain secret. -/
theorem raw_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {hs hp ho hh hf : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0]) (.block (Square.squareSetup a)) hs).isSome = true)
    (hP : (taint.check (Taint.ofRegs [.x0, .x8, .x12, .x7]) (preparation a) hp).isSome = true)
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0]) (.block (finishRaw a)) hf).isSome = true) :
    RelCT isa (Two FastW) (SquareEightRaw.raw a) (Two RedcPreCtx) := by
  unfold SquareEightRaw.raw
  refine RelCT.seq (two_piece _ ProductEight.pins_fast hS (ProductEight.setup_fast_ctx ha)) ?_
  apply RelCT.assoc
  exact RelCT.seq (two_piece _ (ProductEight.pins_setup a) hP (preparation_ctx ha))
    (RelCT.seq (rows_ct ha ha1 ha2 hO hH)
      (RelCT.seq (two_piece _ (pins_final a) hF (finishRaw_ctx ha))
        (two_piece _ (pins_diagonal a) (by taint_decide) (diagonal_ctx ha ha1 ha2))))

/-- Full constant-time Montgomery squaring, including the existing final
canonical subtraction and masked selection. -/
theorem square_ct {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {hs hp ht hh hf he hv : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0]) (.block (Square.squareSetup a)) hs).isSome = true)
    (hP : (taint.check (Taint.ofRegs [.x0, .x8, .x12, .x7]) (preparation a) hp).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ht).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0]) (.block (finishRaw a)) hf).isSome = true)
    (hE : (taint.check (Taint.ofRegs [.x0]) (.block (Square.finishBases o)) he).isSome = true)
    (hV : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr o)]) hv).isSome = true) :
    RelCT isa (Two FastW) (SquareEightRaw.square o a) (fun _ _ => True) := by
  unfold SquareEightRaw.square
  refine RelCT.seq (raw_ct ha ha1 ha2 hS hP hT hH hF) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.fast.1)
    (BlockedRedc.saves_ct ho hV)) (ProductEight.spill_ctx ho)) ?_
  refine RelCT.seq (two_post BlockedRedc.redc_ct BlockedRedc.redc_fast_ctx) ?_
  refine RelCT.seq (R := Two (Square.FinCtx o)) ?_ (FastFinish.finish_ct o)
  apply RelCT.block_append
  exact RelCT.seq (two_post (two_map id (fun _ _ h => h.1.good.1)
    (BlockedRedc.restores_ct ho hV)) (BlockedRedc.restores_ctx ho))
    (two_piece _ Square.pins_red hE (Square.finish_bases_ctx ho))

end VG.Proof.Bignum.AArch64.SquareEight
