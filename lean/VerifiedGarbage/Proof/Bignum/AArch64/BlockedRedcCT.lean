module

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64

structure RedcPreCtx (L : Ws) (s : State) : Prop where
  fast : FastW L s
  ptr : s.gpr .x8 = off L.B (rawBase L)
  count : s.gpr .x12 = BitVec.ofNat 64 L.w
  zero : s.gpr .x7 = 0

abbrev EndCtx (L : Ws) (s : State) := LoopCtx L (blocks L) s

def EndPtr (L : Ws) (s : State) : Prop :=
  GoodW L s ∧ s.gpr .x16 = off L.B (rowBase L (blocks L) + 8 * L.w)

theorem pins_pre : Pins RedcPreCtx [.x12] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  exact hs.count.trans ht.count.symm

theorem init_ctx (L : Ws) (s : State) (h : RedcPreCtx L s) :
    WP isa (.block [.lsr .x .x12 .x12 3, movi .x10 0]) s
      (fun t => 0 < blocks L ∧ LoopCtx L 0 t) := by
  have hw := Square.goodW_width h.fast.1
  have he : 8 * blocks L = L.w := by have := h.fast.2.2; dsimp [blocks]; omega
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  refine WP.mono (redcInit_ok (h.count.trans (congrArg (BitVec.ofNat 64) he.symm))
    (by omega)) fun t ⟨⟨ht12, ht10, hm⟩, kt⟩ => ?_
  refine ⟨by have := h.fast.2.1; dsimp [blocks]; omega,
    ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
      hm ▸ hg.hdr⟩, hz⟩, h.fast.2⟩,
      (kt.gpr .x8 (by decide)).trans h.ptr, ht12,
      (kt.gpr .x7 (by decide)).trans h.zero, ?_⟩⟩
  rw [ht10]; decide

theorem pins_end : Pins EndCtx [.x0, .x8] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact pins_goodW L s t hs.fast.1 ht.fast.1 .x0 (by simp)
  · exact hs.ptr.trans ht.ptr.symm

theorem end_ctx (L : Ws) (s : State) (h : EndCtx L s) :
    WP isa (.block [ldh .x12 sW, .lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16]) s (EndPtr L) := by
  have hw := Square.goodW_width h.fast.1
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  refine WP.mono (endSetup_ok hg.scr hg.x0 h.ptr (by unfold slot hdrBytes at hz; omega)
    (by omega) hg.hdr.hw) fun t ⟨⟨_, ht16, hm⟩, kt⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    hm ▸ hg.hdr⟩, hz⟩, ht16⟩

theorem pins_end_ptr : Pins EndPtr [.x0, .x16] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact pins_goodW L s t hs.1 ht.1 .x0 (by simp)
  · exact hs.2.trans ht.2.symm

theorem redc_ct : RelCT isa (Two RedcPreCtx)
    VG.Impl.Bignum.AArch64.BlockedRedc.redc (fun _ _ => True) := by
  rewrite [redc_code_eq]
  refine RelCT.seq (two_piece _ pins_pre (by taint_decide) init_ctx) (RelCT.seq rows_ct ?_)
  change RelCT isa (Two EndCtx)
    (.block (([ldh .x12 sW, .lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16] : List Instr) ++
      [st .x10 .x16, st .x7 .x16 8, ldh .x10 (sArr aN)])) _
  apply RelCT.block_append
  exact RelCT.seq (two_piece _ pins_end (by taint_decide) end_ctx)
    (two_taint _ pins_end_ptr (by taint_decide))

theorem redc_ctx (L : Ws) (s : State) (h : RedcPreCtx L s) :
    WP isa VG.Impl.Bignum.AArch64.BlockedRedc.redc s (Square.RedCtx L) := by
  have hw := Square.goodW_width h.fast.1
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  refine WP.mono (redc_layout_ok hg.scr hg.x0 hg.hdr hz h.ptr h.count h.zero
    h.fast.2.1 (by omega) h.fast.2.2) fun t ⟨_, ho, ht8, ht10, ht12, ht7, kt⟩ => ?_
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    (Square.scratch_arrays ho).hdr hg.hdr⟩, hz⟩, by have := h.fast.2.1; omega⟩,
    ht8, ht10, ht12, ht7⟩

end VG.Proof.Bignum.AArch64.BlockedRedc
