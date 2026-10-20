module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetupCT
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparsePadding
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.WideZero
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtSetup

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
    (L : Ws) (s : State) (h : RedcPreCtx L s) :
    WP isa (preparation a) s fun t => 0 < blocks L ∧ LoopCtx a b L 0 t := by
  have fast : FastW L s := h.fast
  obtain ⟨he, hk, hk'⟩ := fast_width fast
  obtain ⟨mi, hg, hz⟩ := fast.1
  have hn := hg.scr.nowrap
  have hP : productBase (blocks L) + 8 * (16 * blocks L + 2) ≤ L.Z := by
    unfold productBase
    rw [he]
    unfold slot Public.aAcc at *
    omega
  have h8 : s.gpr .x8 = off L.B (productBase (blocks L)) := by
    simpa only [productBase, he] using h.ptr
  have h12 : s.gpr .x12 = BitVec.ofNat 64 (8 * blocks L) := by rw [he]; exact h.count
  unfold preparation
  refine WP.seq (WP.mono (WideLoops.zero_ok hg.scr h8 h.zero h12 hP hk hk')
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
    hHt⟩, hz⟩, h.fast.2⟩, ht8, ht12, (kall.gpr .x7 (by decide)).trans h.zero, ?_⟩⟩
  rw [htm, hu0]
  simp only [wv, Nat.zero_mul]

def squarePreparation (a : Nat) : Prog isa :=
 .seq (.block VG.Impl.Bignum.AArch64.WindowSparse.padding)
  (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3])

theorem square_preparation_ctx {a : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : RedcPreCtx L s) :
    WP isa (squarePreparation a) s fun t => 0 < blocks L ∧ WindowSparse.LoopCtx a L 0 t := by
  have fast : FastW L s := h.fast
  obtain ⟨he, hk, hk'⟩ := fast_width fast
  obtain ⟨mi, hg, hz⟩ := fast.1
  have hn := hg.scr.nowrap
  have hP : productBase (blocks L) + 8 * (16 * blocks L + 2) ≤ L.Z := by
    unfold productBase
    rw [he]
    unfold slot Public.aAcc at *
    omega
  have h8 : s.gpr .x8 = off L.B (productBase (blocks L)) := by
    simpa only [productBase, he] using h.ptr
  have h12 : s.gpr .x12 = BitVec.ofNat 64 (8 * blocks L) := by rw [he]; exact h.count
  unfold squarePreparation
  refine WP.seq (WP.mono (WindowSparse.padding_ok (e := productBase (blocks L)) hg.scr h8 h12 h.zero (by omega) hk')
    fun u ⟨hu0, huo, ku⟩ => ?_)
  have hlen : 2 * (8 * (blocks L)) = 16 * (blocks L) := by omega
  have hframe := Square.scratch_arrays (s := s) (t := u) (B := L.B) (w := 8 * blocks L)
    (by simpa only [productBase, hlen] using huo.mono (o' := productBase (blocks L)) (n' := 8*(16*blocks L+2)) (by omega) (by omega))
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
    hHt⟩, hz⟩, h.fast.2⟩, ht8, ht12, (kall.gpr .x7 (by decide)).trans h.zero, ?_⟩⟩
  rfl

theorem square_finish_ctx {a : Nat} (ha : a < 8)
    (L : Ws) (s : State) (h : WindowSparse.LoopCtx a L (blocks L) s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowSetup.square a)) s (WindowSetup.DiagCtx a L) :=
  WindowSetup.square_ctx ha L s h.fast h.zero

theorem product_finish_ctx {a b : Nat}
    (L : Ws) (s : State) (h : LoopCtx a b L (blocks L) s) :
    WP isa (.block VG.Impl.Bignum.AArch64.WindowSetup.product) s (RedcPreCtx L) :=
  WindowSetup.product_ctx L s h.fast h.zero

end VG.Proof.Bignum.AArch64.WindowRaw
