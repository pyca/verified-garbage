module

public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCT
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRestore
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRestore
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64

def SpillPtr (o : Nat) (L : Ws) (s : State) : Prop := s.gpr .x16 = off L.B (slot L.w o)

theorem spill_ctx {o : Nat} (ho : o < 8) (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block [ldh .x16 (sArr o)]) s (SpillPtr o L) := by
  obtain ⟨mi, hg, hz⟩ := h
  exact WP.mono (spillBase_ok hg.scr hg.x0 hg.hdr hz ho) fun _ ht => ht.1.1

theorem pins_spill (o : Nat) : Pins (SpillPtr o) [.x16] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  exact hs.trans ht.symm

theorem saves_ct {o : Nat} (ho : o < 8) {hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr o)]) hh).isSome = true) :
    RelCT isa (Two GoodW) (.block (VG.Impl.Bignum.AArch64.BlockedRedc.saves o)) (fun _ _ => True) := by
  change RelCT isa (Two GoodW) (.block ([ldh .x16 (sArr o)] ++ savePrefix 11)) _
  apply RelCT.block_append
  exact RelCT.seq (two_piece _ pins_goodW hH (spill_ctx ho))
    (two_taint _ (pins_spill o) (by taint_decide))

theorem restores_ct {o : Nat} (ho : o < 8) {hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr o)]) hh).isSome = true) :
    RelCT isa (Two GoodW) (.block (VG.Impl.Bignum.AArch64.BlockedRedc.restores o)) (fun _ _ => True) := by
  change RelCT isa (Two GoodW) (.block ([ldh .x16 (sArr o)] ++ restorePrefix 11)) _
  apply RelCT.block_append
  exact RelCT.seq (two_piece _ pins_goodW hH (spill_ctx ho))
    (two_taint _ (pins_spill o) (by taint_decide))

def FastRaw (L : Ws) (s : State) : Prop := Square.RawCtx L s ∧ 16 ≤ L.w ∧ L.w % 8 = 0
def FastRed (L : Ws) (s : State) : Prop := Square.RedCtx L s ∧ 16 ≤ L.w

theorem saves_ctx {o : Nat} (ho : o < 8) (L : Ws) (s : State) (h : FastRaw L s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.saves o)) s (RedcPreCtx L) := by
  obtain ⟨mi, hg, hz⟩ := h.1.good.1
  refine WP.mono (saves_ok hg.scr hg.x0 hg.hdr hz ho h.2.1) fun t ⟨_, hout, kt⟩ => ?_
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    (spill_arrays h.2.1 hout).hdr hg.hdr⟩, hz⟩, h.2⟩,
    (kt.gpr .x8 (by decide)).trans h.1.x8, (kt.gpr .x12 (by decide)).trans h.1.x12,
    (kt.gpr .x7 (by decide)).trans h.1.x7⟩

theorem redc_fast_ctx (L : Ws) (s : State) (h : RedcPreCtx L s) :
    WP isa VG.Impl.Bignum.AArch64.BlockedRedc.redc s (FastRed L) :=
  WP.mono (redc_ctx L s h) fun _ ht => ⟨ht, h.fast.2.1⟩

theorem saved_index : ∀ i < 11,
    VG.Impl.Bignum.AArch64.BlockedRedc.saved.idxOf VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! = i := by decide

theorem restores_ctx {o : Nat} (ho : o < 8) (L : Ws) (s : State) (h : FastRed L s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.restores o)) s (Square.RedCtx L) := by
  obtain ⟨mi, hg, hz⟩ := h.1.good.1
  let g := fun r => word s.mem L.B (slot L.w o + 8 * VG.Impl.Bignum.AArch64.BlockedRedc.saved.idxOf r)
  have hgSaved : ∀ i < 11, word s.mem L.B (slot L.w o + 8 * i) =
      g VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! := by
    intro i hi
    dsimp [g]
    rw [saved_index i hi]
  refine WP.mono (restores_ok hg.scr hg.x0 hg.hdr hz ho h.2 hgSaved) fun t ⟨_, hm, kt⟩ => ?_
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    hm ▸ hg.hdr⟩, hz⟩, h.1.good.2⟩,
    (kt.gpr .x8 (by decide)).trans h.1.x8, (kt.gpr .x10 (by decide)).trans h.1.x10,
    (kt.gpr .x12 (by decide)).trans h.1.x12, (kt.gpr .x7 (by decide)).trans h.1.x7⟩

end VG.Proof.Bignum.AArch64.BlockedRedc
