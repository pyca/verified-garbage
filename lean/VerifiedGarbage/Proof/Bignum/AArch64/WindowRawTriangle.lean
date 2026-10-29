module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowRaw
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparsePadding
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseRows

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

open VG.Proof.Bignum.AArch64.ProductEight (productBase start_ok)
open VG.Proof.Bignum.AArch64.WindowSparse (rows_ok)
open VG.Impl.Bignum.AArch64.WindowRaw

abbrev regs := mmRegs ++ VG.Impl.Bignum.AArch64.ProductEight.regs

/-- Exact triangular product in the existing scratch arrays, without per-operation register saves. No arithmetic input bound is needed. -/
theorem triangle_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8 * k) minv)
    (hZ : slot (8 * k) 8 ≤ Z) (hk : 0 < k) (hk' : k < 2 ^ 56)
    {a : Nat} (ha : a < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    WP isa (triangle a) s fun t =>
      wv t.mem B (productBase k) (16 * k + 2) =
        Square.crossValue s.mem B (slot (8*k) a) (8*k) ∧
      Outside B (productBase k) (8 * (16 * k + 2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧ t.gpr .x9 = off B (slot (8*k) a) ∧
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
  unfold triangle
  refine WP.seq (WP.mono (WindowSetup.start_ok hs h0 hH hZ)
    fun u ⟨⟨hu8, hu12, hu7, hum⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (WindowSparse.padding_ok (e := productBase k) (hs.congr ku.wr) hu8 hu12 hu7 (by omega) hk')
    fun v ⟨hv0, hvo, kv⟩ => ?_)
  have ksv := ku.trans kv
  have hvs : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v.mem := by
    intro x hx
    exact (hvo x (by omega)).trans (congrArg (fun m : Mem => m x) hum)
  have hHv : Hdr v.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega] using hvs)).hdr hH
  refine WP.seq (WP.mono (start_ok (hs.congr ksv.wr)
    ((ksv.gpr .x0 (by decide)).trans h0) hHv hZ ha hk'
    ((kv.gpr .x12 (by decide)).trans hu12))
    fun v1 ⟨⟨hv18, hv112, hv1m, hv1v⟩, kstart⟩ => ?_)
  have kpre := ksv.trans kstart
  have hv1zero : wv v1.mem B (productBase k+128*k) 2 = 0 := by
    rw [hv1m]; exact hv0
  have hv1H : Hdr v1.mem B (8 * k) minv := by rw [hv1m]; exact hHv
  refine WP.seq (WP.mono (rows_ok (hs.congr kpre.wr)
    ((kpre.gpr .x0 (by decide)).trans h0)
    ((kstart.gpr .x7 (by decide)).trans ((kv.gpr .x7 (by decide)).trans hu7)) hv1H hZ hv18 hv112 ha hk hk'
    (sep a ha ha1 ha2))
    fun v2 ⟨hr, hvec⟩ => ?_)
  have kv3 := kpre.trans hr.keep
  have hvs3 : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v2.mem := by
    have hvs1 : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v1.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hv1m).trans (hvs x hx)
    exact hvs1.trans (hr.frame.mono (by omega) (by omega))
  have hHv3 : Hdr v2.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega] using hvs3)).hdr hH
  refine WP.mono (WindowSetup.square_ok (hs.congr kv3.wr)
    ((kv3.gpr .x0 (by decide)).trans h0) hHv3 hZ ha)
    fun t ⟨⟨ht8, ht9, ht12, htm⟩, kt⟩ => ?_
  have kout := kv3.trans kt
  refine ⟨?_, ?_, ht8, ht9, ht12, (kt.gpr .x7 (by decide)).trans ((hr.keep.gpr .x7 (by decide)).trans ((kstart.gpr .x7 (by decide)).trans ((kv.gpr .x7 (by decide)).trans hu7))), ?_⟩
  · rw [htm,show 16*k+2 = 16*k+2 from rfl,wv_add,
      show productBase k+8*(16*k) = productBase k+128*k by omega,
      hr.frame.wv (d := productBase k+128*k) (k := 2) (by omega) (by omega),hv1zero,
      Nat.mul_zero,Nat.add_zero,hr.value]
    apply Square.crossValue_congr
    intro j hj
    rw [hv1m]
    exact hvs.word (by have := sep a ha ha1 ha2; omega) (by
      have := slot_le (w := 8*k) ha
      omega)
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (hvs3 x hx)
  · exact kout.mono (by decide)

end VG.Proof.Bignum.AArch64.WindowRaw
