module

import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRowMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightColumns
public import VerifiedGarbage.Proof.Bignum.Layout
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc (wv_blocks_succ)

abbrev rawRegs := productColumnRegs ++ [.x8, .x12]
abbrev productBase (k : Nat) := slot (8 * k) Public.aAcc + 16

structure ProductRowsInv (s : State) (B : Addr) (Z k a b i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep rawRegs s t
  ptr : t.gpr .x8 = off B (slot (8 * k) a + 64 * i)
  frame : Outside B (productBase k) (8 * (16 * k + 2)) s.mem t.mem
  value : wv t.mem B (productBase k) (16 * k + 2) =
    wv s.mem B (slot (8 * k) a) (8 * i) * wv s.mem B (slot (8 * k) b) (8 * k)

theorem rowEnd_ok {s : State} {B : Addr} {e : Nat} (h8 : s.gpr .x8 = off B e) :
    WP isa (.block [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]) s fun t =>
      (t.gpr .x8 = off B (e + 64) ∧ t.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1 ∧
        t.mem = s.mem) ∧ Keep [.x8, .x12] s t := by
  refine WP.keep [.x8, .x12] ?_ rfl rfl rfl
  brun [h8]

/-- The eight-limb outer row preserves the complete product, including padding. -/
theorem productRow_ok {s t : State} {B : Addr} {Z k a b i : Nat} {minv : BitVec 64}
    (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0) (hH : Hdr s.mem B (8 * k) minv)
    (hZ : slot (8 * k) 8 ≤ Z) (ha : a < 8) (hb : b < 8)
    (hk : k < 2 ^ 56) (hi : i < k)
    (hA : slot (8 * k) a + 64 * k ≤ productBase k ∨
      productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) a)
    (hB : slot (8 * k) b + 64 * k ≤ productBase k ∨
      productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) b)
    (hI : ProductRowsInv s B Z k a b i t) :
    WP isa (.seq (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b))
      (.seq (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock)
        (.block [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))) t fun u =>
      ProductRowsInv s B Z k a b (i + 1) u ∧
        u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have hP : productBase k + 8 * (16 * k + 2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega_arith
  have haZ : slot (8 * k) a + 64 * k ≤ Z := by
    have := slot_le (w := 8 * k) ha
    omega_arith
  have hbZ : slot (8 * k) b + 64 * k ≤ Z := by
    have := slot_le (w := 8 * k) hb
    omega_arith
  have hHt : Hdr t.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega_arith] using hI.frame)).hdr hH
  refine WP.seq (WP.mono (rowSetup_ok hI.scr
    ((hI.keep.gpr .x0 (by decide)).trans h0) hHt hZ ha hb hk hI.ptr)
    fun v ⟨⟨hv16, hv17, hv15, hv10, hvm⟩, kv⟩ => ?_)
  have hv8 := (kv.gpr .x8 (by decide)).trans hI.ptr
  have hv7 := (kv.gpr .x7 (by decide)).trans ((hI.keep.gpr .x7 (by decide)).trans h7)
  have hq := hI.frame.wv (d := slot (8 * k) a + 64 * i) (k := 8) (by omega_arith) (by omega_arith)
  have hbv := hI.frame.wv (d := slot (8 * k) b) (k := 8 * k) (by omega_arith) (by omega_arith)
  have hbSlice : wv v.mem B (productBase k + 64 * i) (8 * (k + 1)) ≤
      wv v.mem B (slot (8 * k) b) (8 * k) := by
    have hw := wv_window_le t.mem B (productBase k) (16 * k + 2) (8 * i) (8 * (k + 1)) (by omega_arith)
    rw [hI.value] at hw
    have hbnd := row_window_bound (by exact Nat.two_pow_pos _)
      (wv_lt s.mem B (slot (8 * k) a) (8 * i)) hw
    simpa only [hvm, hbv, show 8 * (8 * i) = 64 * i by omega_arith] using hbnd
  refine WP.seq (WP.mono (productColumns_bounded (eT := productBase k + 64 * i) (hI.scr.congr kv.wr) hv8 hv7 hv10 hv16 hv17 hv15
    (by omega_arith) (by omega_arith) hbZ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hbSlice)
    fun v' ⟨hC, _, hcv⟩ => ?_)
  have hv'8 := (hC.keep.gpr .x8 (by decide)).trans hv8
  refine WP.mono (rowEnd_ok hv'8) fun u ⟨⟨hu8, hu12, hum⟩, ku⟩ => ?_
  have hframe := wv_window_delta (n := 16 * k + 2) (j := 8 * i) (k := 8 * (k + 1))
    (by omega_arith : productBase k + 8 * (16 * k + 2) ≤ 2 ^ 64) (by omega_arith)
    (by simpa only [show 8 * (8 * i) = 64 * i by omega_arith,
      show 8 * (8 * (k + 1)) = 64 * (k + 1) by omega_arith] using hC.frame)
  have hcv' := hcv
  rewrite [hvm, hq, hbv] at hcv'
  have hh := hframe
  rewrite [show 8 * (8 * i) = 64 * i by omega_arith, hvm] at hh
  have he := row_value hh hcv' hI.value
  refine ⟨⟨hI.scr.congr (ku.wr.trans (hC.keep.wr.trans kv.wr)),
    (((hI.keep.trans kv).trans hC.keep).trans ku).mono (by decide),
    hu8.trans (congrArg (off B) (by omega_arith)), ?_, ?_⟩, ?_⟩
  · have ho : Outside B (productBase k + 64 * i) (64 * (k + 1)) t.mem u.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hum).trans
        ((hC.frame x hx).trans (congrArg (fun m : Mem => m x) hvm))
    exact hI.frame.trans (ho.mono (by omega_arith) (by omega_arith))
  · rewrite [hum, wv_blocks_succ]
    exact he
  · exact hu12.trans (congrArg (· - BitVec.ofNat 64 1)
      ((hC.keep.gpr .x12 (by decide)).trans (kv.gpr .x12 (by decide))))

theorem rows_noVec (a b : Nat) :
    (VG.Impl.Bignum.AArch64.ProductEight.rows a b).allInstrs
      (fun i => (vdstOf i).isNone) = true := by
  rfl

/-- Exact full multiplication for every positive supported tile count. -/
theorem productRows_ok {s : State} {B : Addr} {Z k a b : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8 * k) minv) (hZ : slot (8 * k) 8 ≤ Z)
    (h8 : s.gpr .x8 = off B (slot (8 * k) a)) (h12 : s.gpr .x12 = BitVec.ofNat 64 k)
    (ha : a < 8) (hb : b < 8) (hk : 0 < k) (hk' : k < 2 ^ 56)
    (hA : slot (8 * k) a + 64 * k ≤ productBase k ∨
      productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) a)
    (hB : slot (8 * k) b + 64 * k ≤ productBase k ∨
      productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) b)
    (hz : wv s.mem B (productBase k) (16 * k + 2) = 0) :
    WP isa (VG.Impl.Bignum.AArch64.ProductEight.rows a b) s fun t =>
      ProductRowsInv s B Z k a b k t ∧ ∀ v, t.v v = s.v v := by
  have hinit : ProductRowsInv s B Z k a b 0 s := by
    refine ⟨hs, Keep.refl _ _, h8, Outside.refl _ _ _ _, ?_⟩
    simpa only [Nat.mul_zero, wv, Nat.zero_mul] using hz
  have hp : WP isa (VG.Impl.Bignum.AArch64.ProductEight.rows a b) s
      (ProductRowsInv s B Z k a b k) :=
    wp_countdown (by omega_arith) hk (ProductRowsInv s B Z k a b)
      (fun i hi t hI _ => productRow_ok h0 h7 hH hZ ha hb hk' hi hA hB hI) hinit h12
  obtain ⟨tr, t, he, ht⟩ := hp
  refine ⟨tr, t, he, ht, fun v => Exec.vec ?_ he⟩
  have hc := rows_noVec a b
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  intro i hi h
  have hn := hc i hi
  rw [h] at hn
  contradiction

end VG.Proof.Bignum.AArch64.ProductEight
