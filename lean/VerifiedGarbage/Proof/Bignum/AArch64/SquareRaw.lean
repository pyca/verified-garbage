module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

import VerifiedGarbage.Proof.Bignum.AArch64.SquareCross
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalLoop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The exact unreduced square, with unchanged header and input. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Bignum.Public VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem squareSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) {a : Nat} (ha : a < 8) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) s fun t =>
      (t.gpr .x8 = off B (slot w aAcc+16) ∧ t.gpr .x9 = off B (slot w a) ∧
        t.gpr .x10 = off B (slot w aN) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
        t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x8, .x9, .x10, .x12, .x15, .x7] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8*i)) 8 :=
    fun i hi => hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  refine WP.keep [.x8, .x9, .x10, .x12, .x15, .x7] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.squareSetup
  brun [h0, hdr_enc (sa a ha), hl _ (sa a ha),
    hl _ (sa aAcc (by decide)), hl _ (sa aN (by decide)), hl sW (by decide), hl sMinv (by decide),
    hH.harr aAcc (by decide), hH.harr a ha, hH.harr aN (by decide), hH.hw, hH.hminv]

/-- Exact `a²` in `2w` words and two zero padding words in the existing arrays. -/
theorem rawSquare_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 60)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.Square.rawSquare a) s fun t =>
      wv t.mem B (slot w aAcc+16) (2*w+2) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc+16) (2*w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w aAcc+16) (8*(2*w+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (slot w aAcc+16) ∧ t.gpr .x10 = off B (slot w aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧
      t.gpr .x16 = off B (slot w aAcc+16+16*w) ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  let A := slot w aAcc+16
  let eb := slot w a
  have hA : A+8*(2*w+2) ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold A slot aAcc aTmp at *; omega
  have hb : eb+8*w ≤ Z := by have := slot_le (w := w) ha; omega
  have sb : eb+8*w ≤ A ∨ A+8*(2*w+2) ≤ eb := by
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    unfold A eb slot aAcc aTmp at *; omega
  unfold VG.Impl.Bignum.AArch64.Square.rawSquare
  refine WP.seq (WP.mono (squareSetup_ok hs h0 hH hZ ha)
    fun u ⟨⟨h8, h9, h10, h12, h15, h7, hm⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (cross_ok (hs.congr ku.wr) h8 h9 h12 h7 hw1 hw hA hb sb)
    fun v ⟨hv, ho, hz, kv⟩ => ?_)
  rw [hm] at hv ho
  have kAll := ku.trans kv
  have read : ∀ j < w, word v.mem B (eb+8*j) = word s.mem B (eb+8*j) :=
    fun j hj => ho.word (by omega) (by omega)
  have lower : wv v.mem B A (2*w) = crossValue s.mem B eb w := by
    have upper : wv v.mem B (A+8*(2*w)) 2 = 0 := wv_zero fun j hj => by
      rw [show A+8*(2*w)+8*j = A+8*(2*w+j) by omega]
      exact hz _ (by omega) (by omega)
    rw [wv_add, upper, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  have v8 := (kv.gpr .x8 (by decide)).trans h8
  have v9 := (kv.gpr .x9 (by decide)).trans h9
  have v12 := (kv.gpr .x12 (by decide)).trans h12
  have v7 := (kv.gpr .x7 (by decide)).trans h7
  refine WP.mono (diagonal_ok (hs.congr kAll.wr) v8 v9 v12 v7 (by omega) hw
    (by omega) hb (by omega)) fun t ⟨ht, hot, ht16, kt⟩ => ?_
  rw [lower, diagonalValue_congr read, square_decomposition] at ht
  have bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128*w) := by
    have hl := wv_lt s.mem B eb w
    have hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64*w+64*w = 128*w by omega] at hp
    exact hp
  have topEq : wv t.mem B A (2*w+1) = wv t.mem B A (2*w) +
      2 ^ (128*w)*(word t.mem B (A+16*w)).toNat := by
    rw [wv, show 64*(2*w) = 128*w by omega, show A+8*(2*w) = A+16*w by omega]
  have topZero : (word t.mem B (A+16*w)).toNat = 0 := by
    rw [topEq] at ht
    by_contra hc
    have hc' : 1 ≤ (word t.mem B (A+16*w)).toNat := by omega
    have hm' := Nat.mul_le_mul_left (2 ^ (128*w)) hc'
    simp only [Nat.mul_one] at hm'
    omega
  have lowEq : wv t.mem B A (2*w) = wv s.mem B eb w * wv s.mem B eb w := by
    rw [topEq, topZero, Nat.mul_zero, Nat.add_zero] at ht
    exact ht
  have pad : word t.mem B (A+8*(2*w+1)) = 0 := by
    rw [hot.word (by omega) (by omega)]
    exact hz _ (by omega) (by omega)
  refine ⟨?_, lowEq, ho.trans (hot.mono (o' := A) (n' := 8*(2*w+2))
    (Nat.le_refl _) (by omega)),
    (kt.gpr .x8 (by decide)).trans v8,
    (kt.gpr .x10 (by decide)).trans ((kv.gpr .x10 (by decide)).trans h10),
    (kt.gpr .x12 (by decide)).trans v12,
    (kt.gpr .x15 (by decide)).trans ((kv.gpr .x15 (by decide)).trans h15),
    (kt.gpr .x7 (by decide)).trans v7, ht16, (kAll.trans kt).mono (by decide)⟩
  rw [show 2*w+2 = (2*w+1)+1 by omega, wv, pad, ht]
  simp [eb]

end VG.Proof.Bignum.AArch64.Square
