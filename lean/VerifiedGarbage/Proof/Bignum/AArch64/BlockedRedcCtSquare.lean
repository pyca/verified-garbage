module

public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64

theorem raw_ctx {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (L : Ws) (s : State) (h : FastW L s) :
    WP isa (VG.Impl.Bignum.AArch64.Square.rawSquare a) s (FastRaw L) := by
  unfold VG.Impl.Bignum.AArch64.Square.rawSquare
  apply WP.seq
  refine WP.mono (Square.setup_ctx ha L s ⟨h.1, by have := h.2.1; omega⟩) fun u hu => ?_
  exact WP.mono (Square.raw_body_ctx ha ha1 ha2 L u hu) fun _ ht => ⟨ht, h.2⟩

theorem raw_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    {hs : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) hs).isSome = true) :
    RelCT isa (Two FastW) (VG.Impl.Bignum.AArch64.Square.rawSquare a) (Two FastRaw) := by
  refine two_post ?_ (raw_ctx ha ha1 ha2)
  refine two_map id (fun L s h => (show Square.GW L s from ⟨h.1, Nat.le_trans (by decide) h.2.1⟩)) ?_
  unfold VG.Impl.Bignum.AArch64.Square.rawSquare
  exact RelCT.seq (two_piece _ Square.pins_gw hS (Square.setup_ctx ha)) (Square.raw_body_ct a)

/-- The complete square has public addresses and branch traces independently
of the modulus, inverse, product, carry bits, and saved register values. -/
theorem square_ct {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    {hs hf hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) hs).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.finishBases o)) hf).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr o)]) hh).isSome = true) :
    RelCT isa (Two FastW) (VG.Impl.Bignum.AArch64.BlockedRedc.square o a) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.BlockedRedc.square
  refine RelCT.seq (raw_ct ha ha1 ha2 hS) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.1.good.1) (saves_ct ho hH))
    (saves_ctx ho)) ?_
  refine RelCT.seq (two_post redc_ct redc_fast_ctx) ?_
  refine RelCT.seq (R := Two (Square.FinCtx o)) ?_ (Square.finish_ct o)
  apply RelCT.block_append
  exact RelCT.seq (two_post (two_map id (fun _ _ h => h.1.good.1) (restores_ct ho hH))
    (restores_ctx ho)) (two_piece _ Square.pins_red hF (Square.finish_bases_ctx ho))

end VG.Proof.Bignum.AArch64.BlockedRedc
