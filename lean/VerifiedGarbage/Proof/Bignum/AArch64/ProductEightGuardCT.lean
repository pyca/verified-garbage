module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
meta import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductDispatch
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc
open VG.Proof.Bignum.AArch64.ProductEight (preparation finishRaw)
open VG.Proof.MlKem.AArch64 (eval_nonzero eval_zero)

theorem guarded_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp) (hu : MmUse o a b)
    {hs hp hh hf he hv : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) hs).isSome = true)
    (hP : (taint.check (Taint.ofRegs [.x0, .x8, .x12, .x7]) (preparation a) hp).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b)) hh).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0]) (.block (finishRaw a)) hf).isSome = true)
    (hE : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.finishBases o)) he).isSome = true)
    (hV : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr o)]) hv).isSome = true) :
    RelCT isa (Two GoodW) (VG.Impl.Bignum.AArch64.ProductDispatch.guarded o a b)
      (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.ProductDispatch.guarded
  refine RelCT.seq (two_piece _ pins_goodW (by taint_decide) guard_ctx) ?_
  refine two_ite (Φ := GuardCtx) ?_ ?_ ?_
  · intro L s t hs ht
    rw [eval_nonzero, eval_nonzero, hs.width, ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro L s t hs ht
      rw [eval_zero, eval_zero, hs.1.rem, ht.1.rem]
    · exact two_map id (fun _ _ h => ⟨h.1.1.good, guard_width h.1.1 h.1.2,
        guard_rem h.1.1 h.2⟩) (ProductEight.multiply_ct ho ha hb ha1 ha2 hb1 hb2 hS hP hH hF hE hV)
    · exact two_map id (fun _ _ h => h.1.1.good) (Mont.calledSquareEight.ct hu)
  · exact two_map id (fun _ _ h => h.1.good) (Mont.calledSquareEight.ct hu)

end VG.Proof.Bignum.AArch64.ProductDispatch
