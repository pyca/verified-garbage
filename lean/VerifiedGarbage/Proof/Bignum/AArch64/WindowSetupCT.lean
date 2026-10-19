module
public import VerifiedGarbage.Impl.Bignum.AArch64.WideLoops
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCT
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSetup

import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.WideDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightProducts

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSetup
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks RedcPreCtx)
open VG.Proof.Bignum.AArch64.ProductEight (fast_width input_separation productBase)
open VG.Proof.Bignum.AArch64.SquareEight (frame_header)

structure DiagCtx (a : Nat) (L : Ws) (s : State) : Prop where
  fast : FastW L s
  x8 : s.gpr .x8 = off L.B (slot L.w Public.aAcc+16)
  x9 : s.gpr .x9 = off L.B (slot L.w a)
  x12 : s.gpr .x12 = BitVec.ofNat 64 L.w
  x7 : s.gpr .x7 = 0

theorem start_ctx (L : Ws) (s : State) (h : FastW L s) :
    WP isa (.block VG.Impl.Bignum.AArch64.WindowSetup.start) s (RedcPreCtx L) := by
  obtain ⟨mi,hg,hz⟩ := h.1
  refine WP.mono (start_ok hg.scr hg.x0 hg.hdr hz) fun t ⟨⟨h8,h12,h7,hm⟩,kt⟩ => ?_
  exact ⟨⟨⟨mi,⟨hg.scr.congr kt.wr,(kt.gpr .x0 (by decide)).trans hg.x0,hm ▸ hg.hdr⟩,hz⟩,h.2⟩,h8,h12,h7⟩

theorem square_ctx {a : Nat} (ha : a < 8) (L : Ws) (s : State) (h : FastW L s)
    (h7 : s.gpr .x7 = 0) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowSetup.square a)) s (DiagCtx a L) := by
  obtain ⟨mi,hg,hz⟩ := h.1
  refine WP.mono (square_ok hg.scr hg.x0 hg.hdr hz ha) fun t ⟨⟨h8,h9,h12,hm⟩,kt⟩ => ?_
  exact ⟨⟨⟨mi,⟨hg.scr.congr kt.wr,(kt.gpr .x0 (by decide)).trans hg.x0,hm ▸ hg.hdr⟩,hz⟩,h.2⟩,
    h8,h9,h12,(kt.gpr .x7 (by decide)).trans h7⟩

theorem product_ctx (L : Ws) (s : State) (h : FastW L s) (h7 : s.gpr .x7 = 0) :
    WP isa (.block VG.Impl.Bignum.AArch64.WindowSetup.product) s (RedcPreCtx L) := by
  obtain ⟨mi,hg,hz⟩ := h.1
  refine WP.mono (product_ok hg.scr hg.x0 hg.hdr hz) fun t ⟨⟨h8,h12,hm⟩,kt⟩ => ?_
  exact ⟨⟨⟨mi,⟨hg.scr.congr kt.wr,(kt.gpr .x0 (by decide)).trans hg.x0,hm ▸ hg.hdr⟩,hz⟩,h.2⟩,
    h8,h12,(kt.gpr .x7 (by decide)).trans h7⟩

theorem pins_start : Pins RedcPreCtx [.x0,.x8,.x12,.x7] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_goodW L s t hs.fast.1 ht.fast.1 .x0 (by simp)
  · exact hs.ptr.trans ht.ptr.symm
  · exact hs.count.trans ht.count.symm
  · exact hs.zero.trans ht.zero.symm

theorem pins_diagonal (a : Nat) : Pins (DiagCtx a) [.x8,.x9,.x12] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.x8.trans ht.x8.symm
  · exact hs.x9.trans ht.x9.symm
  · exact hs.x12.trans ht.x12.symm

theorem diagonal_ctx {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (L : Ws) (s : State) (h : DiagCtx a L s) :
    WP isa VG.Impl.Bignum.AArch64.WideLoops.diagonal s (RedcPreCtx L) := by
  have fast : FastW L s := h.fast
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
    simpa only [productBase, he] using h.x8
  have h9 : s.gpr .x9 = off L.B (slot (8*blocks L) a) := by rw [he]; exact h.x9
  have h12 : s.gpr .x12 = BitVec.ofNat 64 (4*(2*blocks L)) := by
    rw [show 4*(2*blocks L) = 8*blocks L by omega, he]
    exact h.x12
  refine WP.mono (WideLoops.diagonal_ok hg.scr h8 h9 h12 h.x7 (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun t ⟨_, hto, _, kt⟩ => ?_
  have hout : Outside L.B (productBase (blocks L)) (8*(16*blocks L+2)) s.mem t.mem :=
    hto.mono (by omega) (by omega)
  have hHt : Hdr t.mem L.B L.w mi := he ▸ frame_header hout (he.symm ▸ hg.hdr)
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr _ (by decide)).trans hg.x0, hHt⟩, hz⟩, h.fast.2⟩,
    (kt.gpr _ (by decide)).trans h.x8, (kt.gpr _ (by decide)).trans h.x12,
    (kt.gpr _ (by decide)).trans h.x7⟩

end VG.Proof.Bignum.AArch64.WindowSetup
