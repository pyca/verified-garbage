module

import VerifiedGarbage.Proof.Framework.OmegaNear
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalLoop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow

/-! The full, unreduced ADX square in the Montgomery working space. -/

@[expose] public section

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
    rw [diagonalValue_succ, diagonalValue_succ, ih (fun j hj => h j (by omega_near)), h w (by omega_near)]

theorem square_decomposition (m : Mem) (B : Addr) (eb w : Nat) :
    2 * crossValue m B eb w + diagonalValue m B eb w = wv m B eb w * wv m B eb w := by
  have h := Square.decomposition (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) w
  rw [value_words] at h
  exact (Nat.add_comm _ _).trans h.symm

/-- A diagonal: doubles the cross products at `A` and adds the squares of
the words at `eb`, for sizes `w` with `P w`. -/
structure DiagOk (diag : Prog isa) (P : Nat → Prop) : Prop where
  ok : ∀ {s : State} {B : Addr} {Z A eb w : Nat}, Scr s B Z →
    s.gpr .r8 = off B A → s.gpr .r9 = off B eb → s.gpr .r10 = BitVec.ofNat 64 w → 0 < w → w < 2^60 →
    P w → A+16*w ≤ Z → eb+8*w ≤ Z → (eb+8*w ≤ A ∨ A+16*w ≤ eb) →
    WP isa diag s fun t =>
      wv t.mem B A (2*w) + 2^(128*w)*(t.gpr .r15).toNat =
        2*wv s.mem B A (2*w) + diagonalValue s.mem B eb w ∧
      Outside B A (16*w) s.mem t.mem ∧
      Keep [.rdx,.r11,.r12,.rsi,.rbx,.rax,.rcx,.r15,.rbp,.r14] s t

theorem diagonalChoice_diag : DiagOk AdxSquare.diagonalChoice (fun _ => True) :=
  ⟨fun hs h8 h9 h10 h0 hw _ hA hb sep => diagonalChoice_ok hs h8 h9 h10 h0 hw hA hb sep⟩

theorem diagonal4_diag : DiagOk AdxSquareGrouped.diagonal (fun w => w % 4 = 0) :=
  ⟨fun hs h8 h9 h10 h0 hw h4 hA hb sep => AdxSquareGrouped.diagonal_ok hs h8 h9 h10 h0 hw h4 hA hb sep⟩

/-- All `2 w` product words are the exact square; the two high padding
words are zero. The input and header are preserved. -/
theorem rawSquareWith_ok {diag : Prog isa} {P : Nat → Prop} (hd : DiagOk diag P)
    {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (hP : P w)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxSquare.rawSquareWith diag a) s fun t =>
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
    omega_near
  have hb : eb + 8 * w ≤ Z := by have := slot_le (w := w) ha; omega_near
  have sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb := by
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    unfold A eb slot aAcc aTmp at *
    omega_near
  have hg : hdrBytes ≤ A := by unfold A slot; omega_near
  unfold AdxSquare.rawSquareWith
  refine WP.seq (WP.mono (adxSetup_ok hs hdi hH hZ ha) fun s₁ ⟨h9₁, _, h8₁, hbx₁, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cross_ok (hs.congr k₁.2.2) h8₁ h9₁ hbx₁ hw1 (by omega_near) hA hb sb)
    fun s₂ ⟨hv₂, ho₂, hz₂, k₂⟩ => ?_)
  rw [hm₁] at hv₂ ho₂
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho₂ hg
  have read₂ : ∀ j < w, word s₂.mem B (eb + 8 * j) = word s.mem B (eb + 8 * j) :=
    fun j hj => ho₂.word (by omega_near) (by omega_near)
  have lo₂ : wv s₂.mem B A (2 * w) = crossValue s.mem B eb w := by
    have zero₂ : wv s₂.mem B (A + 8 * (2 * w)) 2 = 0 := wv_zero fun k hk => by
      rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega_near]
      exact hz₂ _ (by omega_near) (by omega_near)
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
  refine WP.mono (hd.ok (hs.congr k14.2.2) ((k₄.gpr (by decide)).trans h8₃)
    ((k₄.gpr (by decide)).trans h9₃) h10₄ (by omega_near) (by omega_near) hP (by omega_near) hb (by omega_near))
    fun t ⟨hv, ho, kt⟩ => ?_
  rw [hm₄, hm₃] at hv ho
  rw [lo₂, diagonalValue_congr read₂, square_decomposition] at hv
  have bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128 * w) := by
    have hl := wv_lt s.mem B eb w
    have hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_near] at hp
    exact hp
  have carry : (t.gpr .r15).toNat = 0 := by
    by_contra hc
    have hc' : 1 ≤ (t.gpr .r15).toNat := by omega_near
    have hm := Nat.mul_le_mul_left (2 ^ (128 * w)) hc'
    simp only [Nat.mul_one] at hm
    omega_near
  have low : wv t.mem B A (2 * w) = wv s.mem B eb w * wv s.mem B eb w := by
    rw [carry, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  have high : wv t.mem B (A + 8 * (2 * w)) 2 = 0 := wv_zero fun k hk => by
    rw [ho.word (by omega_near) (by omega_near)]
    rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega_near]
    exact hz₂ _ (by omega_near) (by omega_near)
  refine ⟨?_, low, ho₂.trans (ho.mono (o' := A) (n' := 8 * (2 * w + 2)) (Nat.le_refl _) (by omega_near)),
    (k14.trans kt).mono (by decide)⟩
  rw [wv_add, high, Nat.mul_zero, Nat.add_zero]
  exact low

theorem rawSquare_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxSquare.rawSquare a) s fun t =>
      wv t.mem B (slot w aAcc + 16) (2 * w + 2) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t :=
  rawSquareWith_ok diagonalChoice_diag hs hdi hH hZ hw1 hw trivial ha ha1 ha2

end VG.Proof.Bignum.X86_64.AdxSquare
