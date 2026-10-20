module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)

structure LoopCtx (a b : Nat) (L : Ws) (j : Nat) (s : State) : Prop where
  fast : FastW L s
  ptr : s.gpr .x8 = off L.B (slot (8 * blocks L) a + 64 * j)
  count : s.gpr .x12 = BitVec.ofNat 64 (blocks L - j)
  zero : s.gpr .x7 = 0
  value : wv s.mem L.B (productBase (blocks L)) (16 * blocks L + 2) =
    wv s.mem L.B (slot (8 * blocks L) a) (8 * j) *
      wv s.mem L.B (slot (8 * blocks L) b) (8 * blocks L)

structure HeadCtx (a b : Nat) (p : Ws × Nat) (s : State) : Prop where
  loop : LoopCtx a b p.1 p.2 s
  tptr : s.gpr .x16 = off p.1.B (productBase (blocks p.1) + 64 * p.2)
  nptr : s.gpr .x17 = off p.1.B (slot (8 * blocks p.1) b)
  count : s.gpr .x15 = BitVec.ofNat 64 (blocks p.1)

def rowBody (a b : Nat) : Prog isa :=
 .seq (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b))
  (.seq (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock)
    (.block [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))

theorem fast_width {L : Ws} {s : State} (h : FastW L s) :
    8 * blocks L = L.w ∧ 0 < blocks L ∧ blocks L < 2 ^ 56 := by
  obtain ⟨_, hg, hz⟩ := h.1
  have hn := hg.scr.nowrap
  have := h.2
  unfold slot hdrBytes at hz
  dsimp [blocks]
  omega

theorem input_separation {L : Ws} {s : State} (h : FastW L s)
    {a : Nat} (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    slot (8 * blocks L) a + 64 * blocks L ≤ productBase (blocks L) ∨
      productBase (blocks L) + 8 * (16 * blocks L + 2) ≤ slot (8 * blocks L) a := by
  have he := (fast_width h).1
  have := slot_sep (w := L.w) ha1
  have := slot_sep (w := L.w) ha2
  unfold productBase
  rw [he]
  unfold slot Public.aAcc Public.aTmp at *
  omega

theorem head_ctx {a b : Nat} (ha : a < 8) (hb : b < 8)
    (p : Ws × Nat) (s : State) (h : p.2 < blocks p.1 ∧ LoopCtx a b p.1 p.2 s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b)) s (HeadCtx a b p) := by
  obtain ⟨he, _, hk⟩ := fast_width h.2.fast
  obtain ⟨mi, hg, hz⟩ := h.2.fast.1
  have hh : Hdr s.mem p.1.B (8 * blocks p.1) mi := he.symm ▸ hg.hdr
  have hsize : slot (8 * blocks p.1) 8 ≤ p.1.Z := he.symm ▸ hz
  refine WP.mono (rowSetup_ok hg.scr hg.x0 hh hsize ha hb hk h.2.ptr)
    fun t ⟨⟨ht16, ht17, ht15, _, htm⟩, kt⟩ => ?_
  refine ⟨⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    htm ▸ hg.hdr⟩, hz⟩, h.2.fast.2⟩,
    (kt.gpr .x8 (by decide)).trans h.2.ptr, (kt.gpr .x12 (by decide)).trans h.2.count,
    (kt.gpr .x7 (by decide)).trans h.2.zero, ?_⟩, ht16, ht17, ht15⟩
  rw [htm]
  exact h.2.value

theorem row_ctx_next {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp)
    {L : Ws} {j : Nat} {s : State} (hj : j < blocks L) (h : LoopCtx a b L j s) :
    WP isa (rowBody a b) s fun t => LoopCtx a b L (j + 1) t ∧
      isa.eval (.nonzero .x .x12) t = some (decide (j + 1 < blocks L)) := by
  obtain ⟨he, _, hk⟩ := fast_width h.fast
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  have hh : Hdr s.mem L.B (8 * blocks L) mi := he.symm ▸ hg.hdr
  have hsize : slot (8 * blocks L) 8 ≤ L.Z := he.symm ▸ hz
  have hA := input_separation h.fast ha1 ha2
  have hB := input_separation h.fast hb1 hb2
  have hI : ProductRowsInv s L.B L.Z (blocks L) a b j s :=
    ⟨hg.scr, Keep.refl _ _, h.ptr, Outside.refl _ _ _ _, h.value⟩
  refine WP.mono (productRow_ok hg.x0 h.zero hh hsize ha hb hk hj hA hB hI)
    fun t ⟨ht, ht12⟩ => ?_
  have hlen : 2 * (8 * (blocks L)) = 16 * (blocks L) := by omega
  have hframe := Square.scratch_arrays (s := s) (t := t) (B := L.B) (w := 8 * blocks L) (by simpa only [productBase, hlen] using ht.frame)
  have hHt : Hdr t.mem L.B L.w mi := he ▸ hframe.hdr hh
  have hCount : t.gpr .x12 = BitVec.ofNat 64 (blocks L - (j + 1)) := by
    exact (ht12.trans (congrArg (· - BitVec.ofNat 64 1) h.count)).trans
      ((BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)).trans
        (congrArg (BitVec.ofNat 64) (by omega)))
  refine ⟨⟨⟨⟨mi, ⟨ht.scr, (ht.keep.gpr .x0 (by decide)).trans hg.x0, hHt⟩, hz⟩, h.fast.2⟩,
    ht.ptr, hCount, (ht.keep.gpr .x7 (by decide)).trans h.zero, ?_⟩, ?_⟩
  · have hn := hg.scr.nowrap
    have hAZ := slot_le (w := 8 * blocks L) ha
    have hBZ := slot_le (w := 8 * blocks L) hb
    have hqa := ht.frame.wv (d := slot (8 * blocks L) a) (k := 8 * (j + 1)) (by omega) (by omega)
    have hqb := ht.frame.wv (d := slot (8 * blocks L) b) (k := 8 * blocks L) (by omega) (by omega)
    rw [hqa, hqb]
    exact ht.value
  · rw [eval_nonzero, hCount, ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show blocks L - (j + 1) < 2 ^ 64 by omega)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega

end VG.Proof.Bignum.AArch64.ProductEight
