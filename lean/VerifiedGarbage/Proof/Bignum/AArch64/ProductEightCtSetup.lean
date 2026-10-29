module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCT
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext

import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
import VerifiedGarbage.Proof.Bignum.AArch64.WideZero
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSave
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks RedcPreCtx)

abbrev SetupFast (a : Nat) (L : Ws) (s : State) :=
  Square.SetupCtx a L s ∧ 16 ≤ L.w ∧ L.w % 8 = 0

def preparation (a : Nat) : Prog isa :=
 .seq VG.Impl.Bignum.AArch64.WideLoops.zero
  (.block (VG.Impl.Bignum.AArch64.ProductEight.saves ++
    [ldh .x8 (sArr a), .lsr .x .x12 .x12 3]))

def finishRaw (a : Nat) : List Instr :=
 VG.Impl.Bignum.AArch64.ProductEight.restores ++ VG.Impl.Bignum.AArch64.Square.squareSetup a

theorem setup_fast_ctx {a : Nat} (ha : a < 8) (L : Ws) (s : State) (h : FastW L s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) s (SetupFast a L) :=
  WP.mono (Square.setup_ctx ha L s ⟨h.1, by have := h.2.1; omega⟩)
    fun _ ht => ⟨ht, h.2⟩

theorem preparation_ctx {a b : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : SetupFast a L s) :
    WP isa (preparation a) s fun t => 0 < blocks L ∧ LoopCtx a b L 0 t := by
  have fast : FastW L s := ⟨h.1.good.1, h.2⟩
  obtain ⟨he, hk, hk'⟩ := fast_width fast
  obtain ⟨mi, hg, hz⟩ := fast.1
  have hn := hg.scr.nowrap
  have hP : productBase (blocks L) + 8 * (16 * blocks L + 2) ≤ L.Z := by
    unfold productBase
    rw [he]
    unfold slot Public.aAcc at *
    omega
  have h8 : s.gpr .x8 = off L.B (productBase (blocks L)) := by
    simpa only [productBase, he] using h.1.x8
  have h12 : s.gpr .x12 = BitVec.ofNat 64 (8 * blocks L) := by rw [he]; exact h.1.x12
  unfold preparation
  refine WP.seq (WP.mono (WideLoops.zero_ok hg.scr h8 h.1.x7 h12 hP hk hk')
    fun u ⟨hu0, huo, ku⟩ => ?_)
  have hlen : 2 * (8 * (blocks L)) = 16 * (blocks L) := by omega
  have hframe := Square.scratch_arrays (s := s) (t := u) (B := L.B) (w := 8 * blocks L)
    (by simpa only [productBase, hlen] using huo)
  have hh : Hdr u.mem L.B (8 * blocks L) mi := hframe.hdr (he.symm ▸ hg.hdr)
  apply WP.block_append
  refine WP.mono (saves_ok u) fun v ⟨⟨hvm, _⟩, kv⟩ => ?_
  have kuv := ku.trans kv
  refine WP.mono (start_ok (hg.scr.congr kuv.wr)
    ((kuv.gpr .x0 (by decide)).trans hg.x0) (hvm ▸ hh) (he.symm ▸ hz) ha hk'
    ((kuv.gpr .x12 (by decide)).trans h12))
    fun t ⟨⟨ht8, ht12, htm, _⟩, kt⟩ => ?_
  have kall := kuv.trans kt
  have hHt : Hdr t.mem L.B L.w mi := by
    rw [htm, hvm]
    exact he ▸ hh
  refine ⟨hk, ⟨⟨⟨mi, ⟨hg.scr.congr kall.wr, (kall.gpr .x0 (by decide)).trans hg.x0,
    hHt⟩, hz⟩, h.2⟩, ht8, ht12, (kall.gpr .x7 (by decide)).trans h.1.x7, ?_⟩⟩
  rw [htm, hvm, hu0]
  simp only [wv, Nat.zero_mul]

theorem finishRaw_ctx {a b : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : LoopCtx a b L (blocks L) s) :
    WP isa (.block (finishRaw a)) s (RedcPreCtx L) := by
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  unfold finishRaw
  apply WP.block_append
  refine WP.mono (restores_ok s) fun u ⟨⟨hum, _⟩, ku⟩ => ?_
  refine WP.mono (Square.squareSetup_ok (hg.scr.congr ku.wr)
    ((ku.gpr .x0 (by decide)).trans hg.x0) (hum ▸ hg.hdr) hz ha)
    fun t ⟨⟨ht8, _, _, ht12, _, ht7, htm⟩, kt⟩ => ?_
  have kall := ku.trans kt
  have hHt : Hdr t.mem L.B L.w mi := by rw [htm, hum]; exact hg.hdr
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kall.wr, (kall.gpr .x0 (by decide)).trans hg.x0, hHt⟩, hz⟩,
    h.fast.2⟩, ht8, ht12, ht7⟩

end VG.Proof.Bignum.AArch64.ProductEight
