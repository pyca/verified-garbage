module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks RedcPreCtx)

theorem pins_fast : Pins FastW [.x0] := fun L s t hs ht => pins_goodW L s t hs.1 ht.1

theorem pins_setup (a : Nat) : Pins (SetupFast a) [.x0, .x8, .x12, .x7] := by
  intro L s t hs ht r hr
  exact Square.pins_setup a L s t hs.1 ht.1 r
    ((show ∀ r ∈ [.x0, .x8, .x12, .x7], r ∈ [.x0, .x8, .x9, .x10, .x12, .x7] by decide) r hr)

theorem pins_final (a b : Nat) : Pins (fun L s => LoopCtx a b L (blocks L) s) [.x0] :=
  fun L s t hs ht => pins_goodW L s t hs.fast.1 ht.fast.1

/-- The full product's addresses and loop counts depend only on public
workspace data. Every operand, product, and carry remains secret. -/
theorem raw_ct {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp)
    {hs hp hh hf : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) hs).isSome = true)
    (hP : (taint.check (Taint.ofRegs [.x0, .x8, .x12, .x7]) (preparation a) hp).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b)) hh).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0]) (.block (finishRaw a)) hf).isSome = true) :
    RelCT isa (Two FastW) (VG.Impl.Bignum.AArch64.ProductEight.raw a b) (Two RedcPreCtx) := by
  unfold VG.Impl.Bignum.AArch64.ProductEight.raw
  refine RelCT.seq (two_piece _ pins_fast hS (setup_fast_ctx ha)) ?_
  apply RelCT.assoc
  exact RelCT.seq (two_piece _ (pins_setup a) hP (preparation_ctx (b := b) ha))
    (RelCT.seq (rows_ct ha hb ha1 ha2 hb1 hb2 hH)
      (two_piece _ (pins_final a b) hF (finishRaw_ctx ha)))

theorem spill_ctx {o : Nat} (ho : o < 8) (L : Ws) (s : State) (h : RedcPreCtx L s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.saves o)) s (RedcPreCtx L) := by
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  refine WP.mono (BlockedRedc.saves_ok hg.scr hg.x0 hg.hdr hz ho h.fast.2.1)
    fun t ⟨_, hout, kt⟩ => ?_
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    (BlockedRedc.spill_arrays h.fast.2.1 hout).hdr hg.hdr⟩, hz⟩, h.fast.2⟩,
    (kt.gpr .x8 (by decide)).trans h.ptr, (kt.gpr .x12 (by decide)).trans h.count,
    (kt.gpr .x7 (by decide)).trans h.zero⟩

/-- Constant-time product, blocked Montgomery reduction, and final reduction. -/
theorem multiply_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp)
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
    RelCT isa (Two FastW) (VG.Impl.Bignum.AArch64.ProductEight.multiply o a b)
      (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.ProductEight.multiply
  refine RelCT.seq (raw_ct ha hb ha1 ha2 hb1 hb2 hS hP hH hF) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.fast.1)
    (BlockedRedc.saves_ct ho hV)) (spill_ctx ho)) ?_
  refine RelCT.seq (two_post BlockedRedc.redc_ct BlockedRedc.redc_fast_ctx) ?_
  refine RelCT.seq (R := Two (Square.FinCtx o)) ?_ (FastFinish.finish_ct o)
  apply RelCT.block_append
  exact RelCT.seq (two_post (two_map id (fun _ _ h => h.1.good.1)
    (BlockedRedc.restores_ct ho hV)) (BlockedRedc.restores_ctx ho))
    (two_piece _ Square.pins_red hE (Square.finish_bases_ctx ho))

end VG.Proof.Bignum.AArch64.ProductEight
