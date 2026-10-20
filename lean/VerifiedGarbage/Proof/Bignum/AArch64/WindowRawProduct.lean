module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
import VerifiedGarbage.Proof.Bignum.AArch64.WideZero

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

open VG.Proof.Bignum.AArch64.ProductEight (productBase start_ok productRows_ok low_value)

/-- Exact full product in the existing scratch arrays, without per-operation register saves. No arithmetic input bound is needed. -/
theorem product_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8 * k) minv)
    (hZ : slot (8 * k) 8 ≤ Z) (hk : 0 < k) (hk' : k < 2 ^ 56)
    {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.WindowRaw.product a b) s fun t =>
      wv t.mem B (productBase k) (16 * k + 2) =
        wv s.mem B (slot (8 * k) a) (8 * k) * wv s.mem B (slot (8 * k) b) (8 * k) ∧
      Outside B (productBase k) (8 * (16 * k + 2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8 * k) ∧ t.gpr .x7 = 0 ∧
      Keep regs s t := by
  have hn := hs.nowrap
  have hP : productBase k + 8 * (16 * k + 2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have sep : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp →
      slot (8 * k) j + 64 * k ≤ productBase k ∨
        productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) j := by
    intro j hj hj1 hj2
    have := slot_sep (w := 8 * k) hj1
    have := slot_sep (w := 8 * k) hj2
    unfold productBase slot Public.aAcc Public.aTmp at *
    omega
  unfold VG.Impl.Bignum.AArch64.WindowRaw.product
  refine WP.seq (WP.mono (WindowSetup.start_ok hs h0 hH hZ)
    fun u ⟨⟨hu8, hu12, hu7, hum⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (WideLoops.zero_ok (hs.congr ku.wr) hu8 hu7 hu12 hP hk hk')
    fun v ⟨hv0, hvo, kv⟩ => ?_)
  have ksv := ku.trans kv
  have hvs : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v.mem := by
    intro x hx
    exact (hvo x hx).trans (congrArg (fun m : Mem => m x) hum)
  have hHv : Hdr v.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega] using hvs)).hdr hH
  refine WP.seq (WP.mono (start_ok (hs.congr ksv.wr)
    ((ksv.gpr .x0 (by decide)).trans h0) hHv hZ ha hk'
    ((kv.gpr .x12 (by decide)).trans hu12))
    fun v1 ⟨⟨hv18, hv112, hv1m, hv1v⟩, kstart⟩ => ?_)
  have kpre := ksv.trans kstart
  have hv1zero : wv v1.mem B (productBase k) (16 * k + 2) = 0 := by
    rw [hv1m]
    exact hv0
  have hv1H : Hdr v1.mem B (8 * k) minv := by rw [hv1m]; exact hHv
  refine WP.seq (WP.mono (productRows_ok (hs.congr kpre.wr)
    ((kpre.gpr .x0 (by decide)).trans h0)
    ((kstart.gpr .x7 (by decide)).trans ((kv.gpr .x7 (by decide)).trans hu7)) hv1H hZ hv18 hv112 ha hb hk hk'
    (sep a ha ha1 ha2) (sep b hb hb1 hb2) hv1zero)
    fun v2 ⟨hr, hvec⟩ => ?_)
  have kv3 := kpre.trans hr.keep
  have hvs3 : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v2.mem := by
    have hvs1 : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v1.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hv1m).trans (hvs x hx)
    exact hvs1.trans hr.frame
  have hHv3 : Hdr v2.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega] using hvs3)).hdr hH
  refine WP.mono (WindowSetup.product_ok (hs.congr kv3.wr)
    ((kv3.gpr .x0 (by decide)).trans h0) hHv3 hZ)
    fun t ⟨⟨ht8, ht12, htm⟩, kt⟩ => ?_
  have kout := kv3.trans kt
  refine ⟨?_, ?_, ht8, ht12, (kt.gpr .x7 (by decide)).trans ((hr.keep.gpr .x7 (by decide)).trans ((kstart.gpr .x7 (by decide)).trans ((kv.gpr .x7 (by decide)).trans hu7))), ?_⟩
  · have hread : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp →
        wv v1.mem B (slot (8 * k) j) (8 * k) = wv s.mem B (slot (8 * k) j) (8 * k) := by
      intro j hj hj1 hj2
      have hjZ := slot_le (w := 8 * k) hj
      rw [hv1m]
      exact hvs.wv (by have := sep j hj hj1 hj2; omega) (by omega)
    rw [htm, hr.value, hread a ha ha1 ha2, hread b hb hb1 hb2]
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (hvs3 x hx)
  · exact kout.mono (by decide)

/-- The public-width form used by Montgomery callers, including the low
product needed by reduction and the full scratch frame. -/
theorem product_width_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2 ^ 31) (hmod : w % 8 = 0)
    {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.WindowRaw.product a b) s fun t =>
      wv t.mem B (slot w Public.aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w ∧
      Outside B (slot w Public.aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧
      t.gpr .x8 = off B (slot w Public.aAcc + 16) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ Keep regs s t := by
  have he : w = 8 * (w / 8) := by omega
  have hH' : Hdr s.mem B (8 * (w / 8)) minv := he ▸ hH
  have hZ' : slot (8 * (w / 8)) 8 ≤ Z := he ▸ hZ
  refine WP.mono (product_ok hs h0 hH' hZ' (by omega) (by omega) ha hb ha1 ha2 hb1 hb2)
    fun t ⟨hv, ho, h8, h12, h7, kt⟩ => ?_
  have hlen : 16 * (w / 8) + 2 = 2 * w + 2 := by omega
  simp only [productBase, ← he, hlen] at hv ho h8 h12
  refine ⟨low_value hv ?_, ho, h8, h12, h7, kt⟩
  have hp := Nat.mul_lt_mul'' (wv_lt s.mem B (slot w a) w) (wv_lt s.mem B (slot w b) w)
  rw [← Nat.pow_add, show 64 * w + 64 * w = 64 * (2 * w) by omega] at hp
  exact hp

end VG.Proof.Bignum.AArch64.WindowRaw
