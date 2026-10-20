module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSparse
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows

import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseHead
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTail
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightOffDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)

open VG.Proof.Bignum.AArch64.SquareEight

abbrev rawRegs := ProductEight.rawRegs

structure RowsInv (s : State) (B : Addr) (Z k a i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep rawRegs s t
  ptr : t.gpr .x8 = off B (slot (8*k) a+64*i)
  frame : Outside B (productBase k) (128*i) s.mem t.mem
  value : wv t.mem B (productBase k) (16*i) = Square.crossValue s.mem B (slot (8*k) a) (8*i)

theorem frame_header {s t : State} {B : Addr} {k : Nat} {minv : BitVec 64}
    (ho : Outside B (productBase k) (8*(16*k+2)) s.mem t.mem)
    (hh : Hdr s.mem B (8*k) minv) : Hdr t.mem B (8*k) minv :=
  (Square.scratch_arrays (by simpa only [productBase, show 2*(8*k) = 16*k by omega] using ho)).hdr hh

/-- A full triangular row adds its internal products and every earlier tile,
then proves that the discarded final carry is zero. -/
theorem row_ok {s t : State} {B : Addr} {Z k a i : Nat} {minv : BitVec 64}
    (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0) (hH : Hdr s.mem B (8*k) minv)
    (hZ : slot (8*k) 8 ≤ Z) (ha : a < 8) (hk : k < 2 ^ 56) (hi : i < k)
    (hA : slot (8*k) a+64*k ≤ productBase k ∨ productBase k+8*(16*k+2) ≤ slot (8*k) a)
    (hI : RowsInv s B Z k a i t) (h12 : t.gpr .x12 = BitVec.ofNat 64 (k-i)) :
    WP isa (.seq (.block (VG.Impl.Bignum.AArch64.WindowSparse.rowHead a))
      (.seq (.ite (.nonzero .x .x15) (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block []))
        (.block (SquareEightRaw.rowTail a)))) t fun u =>
      RowsInv s B Z k a (i+1) u ∧ u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have hP : productBase k+8*(16*k+2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have hAZ : slot (8*k) a+64*k ≤ Z := by
    have := slot_le (w := 8*k) ha
    omega
  refine WP.seq (WP.mono (rowHead_ok hI.scr ((hI.keep.gpr _ (by decide)).trans h0)
    ((hI.keep.gpr _ (by decide)).trans h7) (frame_header (hI.frame.mono (by omega) (by omega)) hH) hZ ha hk hi hI.ptr h12 hA)
    fun v ⟨⟨hvv, hv16, hv17, hv15, hv10, hvo⟩, kv⟩ => ?_)
  have ho1 := (hI.frame.mono (by omega) (by omega)).trans hvo
  have k1 := hI.keep.trans kv
  have hv8 := (kv.gpr _ (by decide)).trans hI.ptr
  have hv7 := (k1.gpr _ (by decide)).trans h7
  have hcInput : Square.crossValue t.mem B (slot (8*k) a+64*i) 8 =
      Square.crossValue s.mem B (slot (8*k) a+64*i) 8 := by
    apply Square.crossValue_congr
    intro j hj
    exact hI.frame.word (by omega) (by omega)
  have h1 := hvv
  rw [hI.value, hcInput] at h1
  refine WP.seq (WP.mono (offDiagonal_full (hI.scr.congr kv.wr) hv8 hv7 hv10 hv16 hv17 hv15
    (by omega) (show productBase k+8*(16*(i+1)) ≤ Z by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun v' ⟨hvv', hvo', kv'⟩ => ?_)
  have ho2 := ho1.trans (hvo'.mono (by omega) (by omega))
  have k2 := k1.trans kv'
  have hq := ho1.wv (d := slot (8*k) a+64*i) (k := 8) (by omega) (by omega)
  have hb := ho1.wv (d := slot (8*k) a) (k := 8*i) (by omega) (by omega)
  have h2 := hvv'
  rw [hq, hb] at h2
  refine WP.mono (rowTail_ok (hI.scr.congr (kv'.wr.trans kv.wr))
    ((k2.gpr _ (by decide)).trans h0) ((k2.gpr _ (by decide)).trans h7)
    (frame_header (ho2.mono (by omega) (by omega)) hH) hZ ha hk hi ((kv'.gpr _ (by decide)).trans hv8))
    fun u ⟨huv, hu8, hu12, huo, ku⟩ => ?_
  have hv := row_finish_value h1 h2 huv
  refine ⟨⟨hI.scr.congr (ku.wr.trans (kv'.wr.trans kv.wr)),
    (k2.trans ku).mono (by decide), hu8, ho2.trans (huo.mono (by omega) (by omega)), hv.1⟩, ?_⟩
  exact hu12.trans (congrArg (· - BitVec.ofNat 64 1)
    ((kv'.gpr _ (by decide)).trans (kv.gpr _ (by decide))))

theorem rows_noVec (a : Nat) :
    (VG.Impl.Bignum.AArch64.WindowSparse.rows a).allInstrs (fun i => (vdstOf i).isNone) = true := by rfl

theorem rows_ok {s : State} {B : Addr} {Z k a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8*k) minv) (hZ : slot (8*k) 8 ≤ Z)
    (h8 : s.gpr .x8 = off B (slot (8*k) a)) (h12 : s.gpr .x12 = BitVec.ofNat 64 k)
    (ha : a < 8) (hk : 0 < k) (hk' : k < 2 ^ 56)
    (hA : slot (8*k) a+64*k ≤ productBase k ∨ productBase k+8*(16*k+2) ≤ slot (8*k) a) :
    WP isa (VG.Impl.Bignum.AArch64.WindowSparse.rows a) s fun t => RowsInv s B Z k a k t ∧ ∀ v, t.v v = s.v v := by
  have hinit : RowsInv s B Z k a 0 s := by
    refine ⟨hs, Keep.refl _ _, h8, Outside.refl _ _ _ _, ?_⟩
    rfl
  have hp : WP isa (VG.Impl.Bignum.AArch64.WindowSparse.rows a) s (RowsInv s B Z k a k) :=
    wp_countdown (by omega) hk (RowsInv s B Z k a)
      (fun i hi t hI hcount => row_ok h0 h7 hH hZ ha hk' hi hA hI hcount) hinit h12
  obtain ⟨tr, t, he, ht⟩ := hp
  refine ⟨tr, t, he, ht, fun v => Exec.vec ?_ he⟩
  have hc := rows_noVec a
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  intro i hi h
  have hn := hc i hi
  rw [h] at hn
  contradiction

end VG.Proof.Bignum.AArch64.WindowSparse
