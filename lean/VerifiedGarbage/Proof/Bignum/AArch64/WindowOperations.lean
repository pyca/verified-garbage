module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowArithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle
import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduce
import VerifiedGarbage.Proof.Bignum.AArch64.WindowReduceCanonical
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
import VerifiedGarbage.Proof.Bignum.AArch64.WideZero

/-! ### `Bignum.AArch64.WindowRawSquare`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)
open VG.Proof.Bignum.AArch64.SquareEight (diagonal_finish_ok)
open VG.Impl.Bignum.AArch64.WindowRaw

theorem raw_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8*k) minv)
    (hZ : slot (8*k) 8 ≤ Z) (hk : 0 < k) (hk' : k < 2 ^ 56)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.WindowRaw.square a) s fun t =>
      wv t.mem B (productBase k) (16*k) =
        wv s.mem B (slot (8*k) a) (8*k) * wv s.mem B (slot (8*k) a) (8*k) ∧
      Outside B (productBase k) (8*(16*k+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8*k) ∧ t.gpr .x7 = 0 ∧ Keep regs s t := by
  have hn := hs.nowrap
  have hP : productBase k+8*(16*k+2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega_using [hZ]
  have hA : slot (8*k) a+64*k ≤ Z := by
    have := slot_le (w := 8*k) ha
    omega_using [hZ, this]
  have sep : slot (8*k) a+64*k ≤ productBase k ∨
      productBase k+8*(16*k+2) ≤ slot (8*k) a := by
    have := slot_sep (w := 8*k) ha1
    have := slot_sep (w := 8*k) ha2
    unfold productBase slot Public.aAcc Public.aTmp at *
    omega_arith
  have hp : WP isa (.seq (triangle a) VG.Impl.Bignum.AArch64.WideLoops.diagonal) s (fun t =>
      wv t.mem B (productBase k) (16*k) =
        wv s.mem B (slot (8*k) a) (8*k) * wv s.mem B (slot (8*k) a) (8*k) ∧
      Outside B (productBase k) (8*(16*k+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8*k) ∧ t.gpr .x7 = 0 ∧ Keep regs s t) :=
    WP.seq (WP.mono (triangle_ok hs h0 hH hZ hk hk' ha ha1 ha2)
      (fun v ⟨hv, ho, h8, h9, h12, h7, kv⟩ => by
        have hcross : Square.crossValue v.mem B (slot (8*k) a) (8*k) =
            Square.crossValue s.mem B (slot (8*k) a) (8*k) := by
          apply Square.crossValue_congr
          intro j hj
          exact ho.word (by omega_using [sep, hj]) (by omega_using [hn, hA, hj])
        have hread := ho.wv (d := slot (8*k) a) (k := 8*k) (by omega_using [sep]) (by omega_using [hn, hA])
        exact WP.mono (diagonal_finish_ok (hs.congr kv.wr) h8 h9 h12 h7 hk hk' hP hA sep
          (hv.trans hcross.symm)) fun t ⟨ht, hto, kt⟩ =>
            ⟨by simpa only [hread] using ht, ho.trans hto,
              (kt.gpr _ (by decide)).trans h8,
              (kt.gpr _ (by decide)).trans h12,
              (kt.gpr _ (by decide)).trans h7, (kv.trans kt).mono (by decide)⟩))
  exact hp

theorem raw_width_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2 ^ 31) (hmod : w % 8 = 0)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.WindowRaw.square a) s fun t =>
      wv t.mem B (slot w Public.aAcc+16) (2*w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w Public.aAcc+16) (8*(2*w+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (slot w Public.aAcc+16) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ Keep regs s t := by
  have he : w = 8*(w/8) := by omega_using [hmod]
  have hH' : Hdr s.mem B (8*(w/8)) minv := he ▸ hH
  have hZ' : slot (8*(w/8)) 8 ≤ Z := he ▸ hZ
  have hlen : 16*(w/8) = 2*w := by omega_using [hmod]
  have hp := raw_ok hs h0 hH' hZ' (by omega_using [hw]) (by omega_using [hw']) ha ha1 ha2
  simpa only [productBase, ← he, hlen] using hp

end VG.Proof.Bignum.AArch64.WindowRaw

end

end

/-! ### `Bignum.AArch64.WindowRawProduct`, which only this module used -/

section

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
    omega_using [hZ]
  have sep : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp →
      slot (8 * k) j + 64 * k ≤ productBase k ∨
        productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) j := by
    intro j hj hj1 hj2
    have := slot_sep (w := 8 * k) hj1
    have := slot_sep (w := 8 * k) hj2
    unfold productBase slot Public.aAcc Public.aTmp at *
    omega_arith
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
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega_using []] using hvs)).hdr hH
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
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega_using []] using hvs3)).hdr hH
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
      exact hvs.wv (by have := sep j hj hj1 hj2; omega_using [this]) (by omega_using [hZ, hn, hjZ])
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
  have he : w = 8 * (w / 8) := by omega_using [hmod]
  have hH' : Hdr s.mem B (8 * (w / 8)) minv := he ▸ hH
  have hZ' : slot (8 * (w / 8)) 8 ≤ Z := he ▸ hZ
  refine WP.mono (product_ok hs h0 hH' hZ' (by omega_using [hw]) (by omega_using [hw']) ha hb ha1 ha2 hb1 hb2)
    fun t ⟨hv, ho, h8, h12, h7, kt⟩ => ?_
  have hlen : 16 * (w / 8) + 2 = 2 * w + 2 := by omega_using [hmod]
  simp only [productBase, ← he, hlen] at hv ho h8 h12
  refine ⟨low_value hv ?_, ho, h8, h12, h7, kt⟩
  have hp := Nat.mul_lt_mul'' (wv_lt s.mem B (slot w a) w) (wv_lt s.mem B (slot w b) w)
  rw [← Nat.pow_add, show 64 * w + 64 * w = 64 * (2 * w) by omega_using []] at hp
  exact hp

end VG.Proof.Bignum.AArch64.WindowRaw

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowArithmetic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem square_ok {s : State} {B : Addr} {Z w a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2^31) (hmod : w % 8 = 0)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (haN : a ≠ aN)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.square a) s fun t =>
      wv t.mem B (slot w a) w * 2^(64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc,aTmp,a] s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  have hn := hs.nowrap
  have hsep : slot w aN+8*(w+2) ≤ slot w aAcc+16 := by unfold slot aN aAcc; omega_arith
  have hnz := slot_le (w := w) (show aN < 8 by decide)
  unfold VG.Impl.Bignum.AArch64.WindowArithmetic.square
  refine WP.seq (WP.mono (WindowRaw.raw_width_ok hs h0 hH hZ hw hw' hmod ha ha1 ha2)
    fun u ⟨hu,ho,h8,h12,h7,ku⟩ => ?_)
  have hHU := (Square.scratch_arrays ho).hdr hH
  have hN : wv u.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho.wv (by omega_arith) (by omega_arith)
  have hi : ((word u.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0 := by
    rw [ho.word (d := slot w aN) (by omega_arith) (by omega_arith)]; exact hinv
  refine WP.mono (lazy_ok (hs.congr ku.wr) ((ku.gpr .x0 (by decide)).trans h0)
    hHU hZ hw hw' hmod h8 h12 h7 ha ha1 ha2 haN hi) fun t ⟨ht,hf,kt⟩ => ?_
  rw [hu,hN] at ht
  exact ⟨ht,((Square.scratch_arrays ho).mono (by simp)).trans hf,(ku.trans kt).mono (by decide)⟩

theorem product_ok {s : State} {B : Addr} {Z w o a b : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2^31) (hmod : w % 8 = 0)
    (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (hoN : o ≠ aN)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb : b < 8) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.product o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2^(64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc,aTmp,o] s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  have hn := hs.nowrap
  have hsep : slot w aN+8*(w+2) ≤ slot w aAcc+16 := by unfold slot aN aAcc; omega_arith
  have hnz := slot_le (w := w) (show aN < 8 by decide)
  unfold VG.Impl.Bignum.AArch64.WindowArithmetic.product
  refine WP.seq (WP.mono (WindowRaw.product_width_ok hs h0 hH hZ hw hw' hmod ha hb ha1 ha2 hb1 hb2)
    fun u ⟨hu,hout,h8,h12,h7,ku⟩ => ?_)
  have hHU := (Square.scratch_arrays hout).hdr hH
  have hN : wv u.mem B (slot w aN) w = wv s.mem B (slot w aN) w := hout.wv (by omega_arith) (by omega_arith)
  have hi : ((word u.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0 := by
    rw [hout.word (d := slot w aN) (by omega_arith) (by omega_arith)]; exact hinv
  have hprod : wv u.mem B (slot w aAcc+16) (2*w) < wv u.mem B (slot w aN) w * 2^(64*w) := by
    rw [hu,hN,Nat.mul_comm (wv s.mem B (slot w a) w)]
    exact Nat.mul_lt_mul'' hB (wv_lt _ _ _ _)
  refine WP.mono (canonical_ok (hs.congr ku.wr) ((ku.gpr .x0 (by decide)).trans h0)
    hHU hZ hw hw' hmod h8 h12 h7 ho ho1 ho2 hoN hi (by rw [hN]; omega_arith) hprod)
    fun t ⟨hlt,ht,hf,kt⟩ => ?_
  rw [hu,hN] at ht
  rw [hN] at hlt
  exact ⟨hlt,ht,((Square.scratch_arrays hout).mono (by simp)).trans hf,(ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WindowArithmetic
