import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalLoop

/-! The full, unreduced ADX square in the Montgomery working space. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem diagonalValue_congr {m m' : Mem} {B : Addr} {eb w : Nat}
    (h : ∀ j < w, word m' B (eb + 8 * j) = word m B (eb + 8 * j)) :
    diagonalValue m' B eb w = diagonalValue m B eb w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [diagonalValue_succ, diagonalValue_succ, ih (fun j hj => h j (by omega)), h w (by omega)]

theorem square_decomposition (m : Mem) (B : Addr) (eb w : Nat) :
    2 * crossValue m B eb w + diagonalValue m B eb w = wv m B eb w * wv m B eb w := by
  have h := Square.decomposition (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) w
  rw [value_words] at h
  exact (Nat.add_comm _ _).trans h.symm

/-- All `2 w` product words are the exact square; the two high padding
words are zero. The input and header are preserved. -/
theorem rawSquare_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxSquare.rawSquare a) s fun t =>
      wv t.mem B (slot w aAcc + 16) (2 * w + 2) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  let A := slot w aAcc + 16
  let eb := slot w a
  have hA : A + 8 * (2 * w + 2) ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold A slot aAcc aTmp at *
    omega
  have hb : eb + 8 * w ≤ Z := by have := slot_le (w := w) ha; omega
  have sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb := by
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    unfold A eb slot aAcc aTmp at *
    omega
  have hg : hdrBytes ≤ A := by unfold A slot; omega
  unfold AdxSquare.rawSquare
  refine WP.seq (WP.mono (adxSetup_ok hs hdi hH hZ ha) fun s₁ ⟨h9₁, _, h8₁, hbx₁, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cross_ok (hs.congr k₁.2.2) h8₁ h9₁ hbx₁ hw1 (by omega) hA hb sb)
    fun s₂ ⟨hv₂, ho₂, hz₂, k₂⟩ => ?_)
  rw [hm₁] at hv₂ ho₂
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho₂ hg
  have read₂ : ∀ j < w, word s₂.mem B (eb + 8 * j) = word s.mem B (eb + 8 * j) :=
    fun j hj => ho₂.word (by omega) (by omega)
  have lo₂ : wv s₂.mem B A (2 * w) = crossValue s.mem B eb w := by
    have zero₂ : wv s₂.mem B (A + 8 * (2 * w)) 2 = 0 := wv_zero fun k hk => by
      rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega]
      exact hz₂ _ (by omega) (by omega)
    rw [wv_add, zero₂, Nat.mul_zero, Nat.add_zero] at hv₂
    exact hv₂
  refine WP.seq (WP.mono (adxSetup_ok hs₂ ((k12.gpr (by decide)).trans hdi) hH₂ hZ ha)
    fun s₃ ⟨h9₃, _, h8₃, hbx₃, hm₃, k₃⟩ => ?_)
  have mov : WP isa (.block [.mov .r10 (.reg .rbx)]) s₃ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem ∧ Keep [.r10] s₃ t := by
    refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem)
      (by xrun [hbx₃]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  refine WP.seq (WP.mono mov fun s₄ ⟨h10₄, hm₄, k₄⟩ => ?_)
  have k14 := (k12.trans k₃).trans k₄
  refine WP.mono (diagonal_ok (hs.congr k14.2.2) ((k₄.gpr (by decide)).trans h8₃)
    ((k₄.gpr (by decide)).trans h9₃) h10₄ (by omega) (by omega) (by omega) hb (by omega))
    fun t ⟨hv, ho, kt⟩ => ?_
  rw [hm₄, hm₃] at hv ho
  rw [lo₂, diagonalValue_congr read₂, square_decomposition] at hv
  have bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128 * w) := by
    have hl := wv_lt s.mem B eb w
    have hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega] at hp
    exact hp
  have carry : (t.gpr .r15).toNat = 0 := by
    by_contra hc
    have hc' : 1 ≤ (t.gpr .r15).toNat := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (128 * w)) hc'
    simp only [Nat.mul_one] at hm
    omega
  have low : wv t.mem B A (2 * w) = wv s.mem B eb w * wv s.mem B eb w := by
    rw [carry, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  have high : wv t.mem B (A + 8 * (2 * w)) 2 = 0 := wv_zero fun k hk => by
    rw [ho.word (by omega) (by omega)]
    rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega]
    exact hz₂ _ (by omega) (by omega)
  refine ⟨?_, low, ho₂.trans (ho.mono (o' := A) (n' := 8 * (2 * w + 2)) (Nat.le_refl _) (by omega)),
    (k14.trans kt).mono (by decide)⟩
  rw [wv_add, high, Nat.mul_zero, Nat.add_zero]
  exact low

end VG.Proof.Bignum.X86_64.AdxSquare
