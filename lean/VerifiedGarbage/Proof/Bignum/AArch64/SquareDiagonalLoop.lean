module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalStep
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Accumulate the full diagonal with its high carry accounted for. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure DiagInv (s₀ : State) (B : Addr) (Z A eb i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (A+16*i)
  x11 : t.gpr .x11 = off B (eb+8*i)
  out : Outside B A (16*i) s₀.mem t.mem
  val : wv t.mem B A (2*i) + 2 ^ (128*i)*(t.gpr .x5).toNat =
    2*wv s₀.mem B A (2*i) + diagonalValue s₀.mem B eb i

theorem diagStep_ok {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h7 : s₀.gpr .x7 = 0) (hi : i < w) (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sb : eb+8*w ≤ A ∨ A+16*w ≤ eb) (hI : DiagInv s₀ B Z A eb i t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.diagonalStep ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
        DiagInv s₀ B Z A eb (i+1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (diagonalStep_ok hI.scr hI.x16 hI.x11 t7 (by omega) (by omega))
    fun u ⟨⟨lo, hiw, hm, hv, _, h16, h11⟩, ku⟩ => ?_
  refine WP.mono (dec_ok u .x14) fun t' ⟨⟨h14, hmem, _⟩, kd⟩ => ?_
  have ho : Outside B (A+16*i) 16 t.mem u.mem := by
    rw [hm]
    exact ((writeW_outside t.mem B lo (d := A+16*i) (by omega)).mono
      (Nat.le_refl _) (by omega)).trans
      ((writeW_outside (t.mem.writeW (off B (A+16*i)) lo) B hiw
        (d := A+16*i+8) (by omega)).mono (by omega) (by omega))
  have rT : wv t.mem B (A+16*i) 2 = wv s₀.mem B (A+16*i) 2 :=
    hI.out.wv (by omega) (by omega)
  have rX : word t.mem B (eb+8*i) = word s₀.mem B (eb+8*i) :=
    hI.out.word (by omega) (by omega)
  have rL : wv u.mem B A (2*i) = wv t.mem B A (2*i) :=
    ho.wv (by omega) (by omega)
  have newPair : wv u.mem B (A+16*i) 2 = lo.toNat + 2 ^ 64*hiw.toNat := by
    rw [hm, wv_writeW_top _ B (A+16*i) 1 hiw (by omega)]
    have hlo := wv_writeW_top t.mem B (A+16*i) 0 lo (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, wv, Nat.zero_add] at hlo
    simp [wv, hlo]
  have pairOld : (word t.mem B (A+16*i)).toNat + 2 ^ 64*(word t.mem B (A+16*i+8)).toNat =
      wv s₀.mem B (A+16*i) 2 := by rw [← rT]; simp [wv, Nat.mul_comm]
  rw [pairOld, rX] at hv
  refine ⟨⟨hI.scr.congr (kd.wr.trans ku.wr),
    (hI.keep.trans (ku.trans kd)).mono (by decide), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kd.gpr .x16 (by decide), h16]; congr 1
  · rw [kd.gpr .x11 (by decide), h11]; congr 1
  · rw [hmem]
    exact (hI.out.mono (o' := A) (n' := 16*(i+1)) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := A) (n' := 16*(i+1)) (by omega) (by omega))
  · rw [hmem, kd.gpr .x5 (by decide)]
    have hold := hI.val
    rw [show 2*(i+1) = 2*i+2 by omega, wv_add, wv_add s₀.mem B A, rL,
      show A+8*(2*i) = A+16*i by omega, newPair,
      show 64*(2*i) = 128*i by omega,
      show 128*(i+1) = 128*i+128 by omega, Nat.pow_add, diagonalValue_succ]
    grind
  · rw [h14, ku.gpr .x14 (by decide)]

/-- All doubled cross products and diagonal squares, including the high word. -/
theorem diagonal_ok {s : State} {B : Addr} {Z A eb w : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B A) (h9 : s.gpr .x9 = off B eb)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hw0 : 0 < w) (hw : w < 2 ^ 60)
    (hA : A+16*w+8 ≤ Z) (hb : eb+8*w ≤ Z)
    (sb : eb+8*w ≤ A ∨ A+16*w+8 ≤ eb) :
    WP isa VG.Impl.Bignum.AArch64.Square.diagonal s fun t =>
      wv t.mem B A (2*w+1) = 2*wv s.mem B A (2*w) + diagonalValue s.mem B eb w ∧
      Outside B A (16*w+8) s.mem t.mem ∧ t.gpr .x16 = off B (A+16*w) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x14, .x16] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.Square.diagonal
  refine WP.seq (WP.mono (WP.keep [.x16, .x11, .x14, .x5] (Q := fun t =>
      t.gpr .x16 = off B A ∧ t.gpr .x11 = off B eb ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x5 = 0 ∧ t.mem = s.mem)
    (by brun [h8, h9, h12]) rfl rfl rfl) fun u ⟨⟨h16, h11, h14, h5, hm⟩, ku⟩ => ?_)
  have u7 := (ku.gpr .x7 (by decide)).trans h7
  have h0 : DiagInv u B Z A eb 0 u :=
    ⟨hs.congr ku.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h11]; rfl,
      Outside.refl _ _ _ _, by simp [wv, h5, diagonalValue, VG.Proof.Bignum.Square.diagonal]⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) hw0 (DiagInv u B Z A eb)
    (fun i hi t hI _ => diagStep_ok u7 hi (by omega) hb (by omega) hI) h0 h14)
    fun v hI => ?_)
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = v.mem.writeW (off B (A+16*w)) (v.gpr .x5))
    (by brun [hI.x16, hI.scr.st (show A+16*w+8 ≤ Z by omega)]) rfl rfl rfl)
    fun t ⟨htm, kt⟩ => ?_
  refine ⟨?_, ?_, (kt.gpr .x16 (by decide)).trans hI.x16, ((ku.trans hI.keep).trans kt).mono (by decide)⟩
  · have hv := hI.val
    rw [hm] at hv
    rw [htm, show A+16*w = A+8*(2*w) by omega,
      wv_writeW_top _ B A (2*w) _ (by omega)]
    simpa only [show 64*(2*w) = 128*w by omega] using hv
  · have ho := hI.out
    rw [hm] at ho
    rw [htm]
    exact (ho.mono (o' := A) (n' := 16*w+8) (Nat.le_refl _) (by omega)).trans
      ((writeW_outside v.mem B (v.gpr .x5) (d := A+16*w) (by omega)).mono (by omega) (by omega))

end VG.Proof.Bignum.AArch64.Square
