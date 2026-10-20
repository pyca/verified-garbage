module

import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)

structure LoopCtx (a : Nat) (L : Ws) (j : Nat) (s : State) : Prop where
  fast : FastW L s
  ptr : s.gpr .x8 = off L.B (slot (8 * blocks L) a + 64 * j)
  count : s.gpr .x12 = BitVec.ofNat 64 (blocks L - j)
  zero : s.gpr .x7 = 0
  value : wv s.mem L.B (productBase (blocks L)) (16 * blocks L + 2) =
    Square.crossValue s.mem L.B (slot (8 * blocks L) a) (8 * j)

open VG.Proof.Bignum.AArch64.ProductEight (productBase fast_width input_separation)

def rowBody (a : Nat) : Prog isa :=
 .seq (.block (SquareEightRaw.rowHead a))
  (.seq (.ite (.nonzero .x .x15) (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block []))
    (.block (SquareEightRaw.rowTail a)))

theorem row_ctx_next {a : Nat} (ha : a < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {L : Ws} {j : Nat} {s : State} (hj : j < blocks L) (h : LoopCtx a L j s) :
    WP isa (rowBody a) s fun t => LoopCtx a L (j + 1) t ∧
      isa.eval (.nonzero .x .x12) t = some (decide (j + 1 < blocks L)) := by
  obtain ⟨he, _, hk⟩ := fast_width h.fast
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  have hh : Hdr s.mem L.B (8 * blocks L) mi := he.symm ▸ hg.hdr
  have hsize : slot (8 * blocks L) 8 ≤ L.Z := he.symm ▸ hz
  have hA := input_separation h.fast ha1 ha2
  have hI : RowsInv s L.B L.Z (blocks L) a j s :=
    ⟨hg.scr, Keep.refl _ _, h.ptr, Outside.refl _ _ _ _, h.value⟩
  refine WP.mono (row_ok hg.x0 h.zero hh hsize ha hk hj hA hI h.count)
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
    have hc : Square.crossValue t.mem L.B (slot (8*blocks L) a) (8*(j+1)) =
        Square.crossValue s.mem L.B (slot (8*blocks L) a) (8*(j+1)) := by
      apply Square.crossValue_congr
      intro i hi
      exact ht.frame.word (by omega) (by omega)
    rw [hc]
    exact ht.value
  · rw [eval_nonzero, hCount, ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show blocks L - (j + 1) < 2 ^ 64 by omega)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega

end VG.Proof.Bignum.AArch64.SquareEight
