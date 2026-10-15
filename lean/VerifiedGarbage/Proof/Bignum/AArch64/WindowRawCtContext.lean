module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks RedcPreCtx)

open VG.Proof.Bignum.AArch64.ProductEight (SetupFast LoopCtx fast_width productBase start_ok)

def preparation (a : Nat) : Prog isa :=
 .seq VG.Impl.Bignum.AArch64.WideLoops.zero
  (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3])

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
  refine WP.mono (start_ok (hg.scr.congr ku.wr)
    ((ku.gpr .x0 (by decide)).trans hg.x0) hh (he.symm ▸ hz) ha hk'
    ((ku.gpr .x12 (by decide)).trans h12))
    fun t ⟨⟨ht8, ht12, htm, _⟩, kt⟩ => ?_
  have kall := ku.trans kt
  have hHt : Hdr t.mem L.B L.w mi := by
    rw [htm]
    exact he ▸ hh
  refine ⟨hk, ⟨⟨⟨mi, ⟨hg.scr.congr kall.wr, (kall.gpr .x0 (by decide)).trans hg.x0,
    hHt⟩, hz⟩, h.2⟩, ht8, ht12, (kall.gpr .x7 (by decide)).trans h.1.x7, ?_⟩⟩
  rw [htm, hu0]
  simp only [wv, Nat.zero_mul]

theorem square_preparation_ctx {a : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : SetupFast a L s) :
    WP isa (preparation a) s fun t => 0 < blocks L ∧ SquareEight.LoopCtx a L 0 t := by
  refine WP.mono (preparation_ctx (b := a) ha L s h) fun t ⟨hk,ht⟩ => ?_
  refine ⟨hk,ht.fast,ht.ptr,ht.count,ht.zero,?_⟩
  simpa only [Nat.mul_zero,wv,Nat.zero_mul,Square.crossValue,VG.Proof.Bignum.Square.cross] using ht.value

theorem square_finish_ctx {a : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : SquareEight.LoopCtx a L (blocks L) s) :
    WP isa (.block (Square.squareSetup a)) s (SetupFast a L) :=
  ProductEight.setup_fast_ctx ha L s h.fast

theorem product_finish_ctx {a b : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : LoopCtx a b L (blocks L) s) :
    WP isa (.block (Square.squareSetup a)) s (RedcPreCtx L) := by
  obtain ⟨mi,hg,hz⟩ := h.fast.1
  refine WP.mono (Square.squareSetup_ok hg.scr hg.x0 hg.hdr hz ha)
    fun t ⟨⟨ht8,_,_,ht12,_,ht7,htm⟩,kt⟩ => ?_
  exact ⟨⟨⟨mi,⟨hg.scr.congr kt.wr,(kt.gpr .x0 (by decide)).trans hg.x0,htm ▸ hg.hdr⟩,hz⟩,
    h.fast.2⟩,ht8,ht12,ht7⟩

end VG.Proof.Bignum.AArch64.WindowRaw
