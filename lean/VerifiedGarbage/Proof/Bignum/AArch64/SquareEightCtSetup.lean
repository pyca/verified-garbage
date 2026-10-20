module
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtContext
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.WideDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSave

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks RedcPreCtx)
open VG.Proof.Bignum.AArch64.ProductEight (SetupFast preparation finishRaw productBase fast_width input_separation)

theorem preparation_ctx {a : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : SetupFast a L s) :
    WP isa (preparation a) s fun t => 0 < blocks L ∧ LoopCtx a L 0 t := by
  refine WP.mono (ProductEight.preparation_ctx (b := a) ha L s h) fun t ⟨hk, ht⟩ => ?_
  refine ⟨hk, ht.fast, ht.ptr, ht.count, ht.zero, ?_⟩
  simpa only [Nat.mul_zero, wv, Nat.zero_mul, Square.crossValue, VG.Proof.Bignum.Square.cross] using ht.value

theorem finishRaw_ctx {a : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : LoopCtx a L (blocks L) s) :
    WP isa (.block (finishRaw a)) s (SetupFast a L) := by
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  apply WP.block_append
  refine WP.mono (ProductEight.restores_ok s) fun u ⟨⟨hum, _⟩, ku⟩ => ?_
  exact ProductEight.setup_fast_ctx ha L u
    ⟨⟨mi, ⟨hg.scr.congr ku.wr, (ku.gpr _ (by decide)).trans hg.x0, hum ▸ hg.hdr⟩, hz⟩, h.fast.2⟩

theorem diagonal_ctx {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (L : Ws) (s : State) (h : SetupFast a L s) :
    WP isa VG.Impl.Bignum.AArch64.WideLoops.diagonal s (RedcPreCtx L) := by
  have fast : FastW L s := ⟨h.1.good.1, h.2⟩
  obtain ⟨he, hk, hk'⟩ := fast_width fast
  obtain ⟨mi, hg, hz⟩ := fast.1
  have hn := hg.scr.nowrap
  have hsize : slot (8*blocks L) 8 ≤ L.Z := he.symm ▸ hz
  have hP : productBase (blocks L)+8*(16*blocks L+2) ≤ L.Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have hA : slot (8*blocks L) a+64*blocks L ≤ L.Z := by
    have := slot_le (w := 8*blocks L) ha
    omega
  have sep := input_separation fast ha1 ha2
  have h8 : s.gpr .x8 = off L.B (productBase (blocks L)) := by
    simpa only [productBase, he] using h.1.x8
  have h9 : s.gpr .x9 = off L.B (slot (8*blocks L) a) := by rw [he]; exact h.1.x9
  have h12 : s.gpr .x12 = BitVec.ofNat 64 (4*(2*blocks L)) := by
    rw [show 4*(2*blocks L) = 8*blocks L by omega, he]
    exact h.1.x12
  refine WP.mono (WideLoops.diagonal_ok hg.scr h8 h9 h12 h.1.x7 (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun t ⟨_, hto, _, kt⟩ => ?_
  have hout : Outside L.B (productBase (blocks L)) (8*(16*blocks L+2)) s.mem t.mem :=
    hto.mono (by omega) (by omega)
  have hHt : Hdr t.mem L.B L.w mi := he ▸ frame_header hout (he.symm ▸ hg.hdr)
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr _ (by decide)).trans hg.x0, hHt⟩, hz⟩, h.2⟩,
    (kt.gpr _ (by decide)).trans h.1.x8, (kt.gpr _ (by decide)).trans h.1.x12,
    (kt.gpr _ (by decide)).trans h.1.x7⟩

end VG.Proof.Bignum.AArch64.SquareEight
