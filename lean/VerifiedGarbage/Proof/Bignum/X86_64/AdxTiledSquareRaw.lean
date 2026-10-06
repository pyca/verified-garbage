import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCross

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem rawSquare_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxTiledSquare.rawSquare a) s fun t =>
      wv t.mem B (slot w aAcc + 16) (2 * w + 2) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w aAcc) (16*w+32) s.mem t.mem ∧ Keep mmRegs s t := by
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
  unfold AdxTiledSquare.rawSquare
  refine WP.seq (WP.mono (rawCross_ok hs hdi hH hZ hw hwN hnN ha ha1 ha2)
    fun s₂ ⟨full₂,lo₂,ho₂,k12⟩ => ?_)
  dsimp only [AdxRect8.rawBase] at full₂ lo₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho₂ (by unfold slot; omega)
  have read₂ : ∀ j < w, word s₂.mem B (eb + 8 * j) = word s.mem B (eb + 8 * j) := by
    intro j hj
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    exact ho₂.word (by unfold eb slot aAcc aTmp at *; omega) (by omega)
  have hz₂ : wv s₂.mem B (A+8*(2*w)) 2=0 := by
    rw [wv_add,lo₂] at full₂
    have pos : 0<2^(64*(2*w)) := Nat.two_pow_pos _
    have zero : 2^(64*(2*w))*wv s₂.mem B (A+8*(2*w)) 2=0 := by
      dsimp only [A]
      omega
    exact (Nat.mul_eq_zero.mp zero).resolve_left (by omega)
  refine WP.seq (WP.mono (adxSetup_ok hs₂ ((k12.gpr (by decide)).trans hdi) hH₂ hZ ha)
    fun s₃ ⟨h9₃, _, h8₃, hbx₃, hm₃, k₃⟩ => ?_)
  have mov : WP isa (.block [.mov .r10 (.reg .rbx)]) s₃ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem ∧ Keep [.r10] s₃ t := by
    refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₃.mem)
      (by xrun [hbx₃]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  refine WP.seq (WP.mono mov fun s₄ ⟨h10₄, hm₄, k₄⟩ => ?_)
  have k14 := (k12.trans k₃).trans k₄
  refine WP.mono (diagonalChoice_ok (hs.congr k14.2.2) ((k₄.gpr (by decide)).trans h8₃)
    ((k₄.gpr (by decide)).trans h9₃) h10₄ (by omega) (by omega) (by omega) hb (by omega))
    fun t ⟨hv, ho, kt⟩ => ?_
  rw [hm₄, hm₃] at hv ho
  rw [lo₂, diagonalValue_congr read₂, square_decomposition] at hv
  have bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128 * w) := by
    have hl := wv_lt s.mem B eb w
    have hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega] at hp
    exact hp
  dsimp only [eb] at bound
  have carry : (t.gpr .r15).toNat = 0 := by
    by_contra hc
    have hc' : 1 ≤ (t.gpr .r15).toNat := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (128 * w)) hc'
    simp only [Nat.mul_one] at hm
    omega
  have low : wv t.mem B A (2 * w) = wv s.mem B eb w * wv s.mem B eb w := by
    rw [carry, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  have high : wv t.mem B (A + 8 * (2 * w)) 2 = 0 := by
    rw [ho.wv (by omega) (by omega)]
    exact hz₂
  refine ⟨?_, low, ho₂.trans (ho.mono (o' := slot w aAcc) (n' := 16*w+32) (by omega) (by omega)),
    (k14.trans kt).mono (by decide)⟩
  rw [wv_add, high, Nat.mul_zero, Nat.add_zero]
  exact low

end VG.Proof.Bignum.X86_64.AdxTiledSquare
