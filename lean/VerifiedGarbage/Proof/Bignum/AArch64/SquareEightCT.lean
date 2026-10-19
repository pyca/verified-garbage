module
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtHead

import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
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
