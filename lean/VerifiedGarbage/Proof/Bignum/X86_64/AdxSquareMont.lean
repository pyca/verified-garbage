import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish

/-! Correctness of Montgomery squaring with BMI2 and ADX. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Montgomery reduction of `X < m R` produces a value below `2 m`. -/
theorem redc_lt {R T X q m : Nat} (hm : 0 < m) (hq : q < R)
    (hX : X < m * R) (he : R * T = X + q * m) : T < 2 * m := by
  have hqm : q * m < R * m := Nat.mul_lt_mul_of_pos_right hq hm
  have hb : R * T < R * (2 * m) := by
    rw [he]
    have h1 : m * R = R * m := Nat.mul_comm _ _
    have h2 : R * (2 * m) = R * m + R * m := by grind
    omega
  exact Nat.lt_of_mul_lt_mul_left hb

/-- Squaring has the same reduced-result, congruence and memory contract as
Montgomery multiplication with equal operands. -/
theorem montSquare_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxSquare.montSquare o a) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hg : hdrBytes ≤ slot w aAcc + 16 := by unfold slot; omega
  have hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hmpos : 0 < wv s.mem B (slot w aN) w := by omega
  unfold AdxSquare.montSquare
  refine WP.seq (WP.mono (rawSquare_ok hs hdi hH hZ hw1 hw ha ha1 ha2) fun s₁ ⟨_, hv₁, ho₁, k₁⟩ => ?_)
  have hH₁ := hH.of_outside ho₁ hg
  have hn₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega) (by omega)
  refine WP.seq (WP.mono (redcChoice_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hH₁ hZ hw1 hw
    (by rw [hn₁]; exact hinv)) fun s₂ ⟨⟨q, hq, heq⟩, ho₂, k₂⟩ => ?_)
  have hN₁ : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho₁.wv (by omega) (by omega)
  rw [hv₁, hN₁] at heq
  have ho12 := (ho₁.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega) (by omega)).trans ho₂
  have hN₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho12.wv (by omega) (by omega)
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho12 (by unfold slot; omega)
  have hTlt : wv s₂.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w :=
    redc_lt hmpos hq (Nat.mul_lt_mul'' hA (wv_lt _ _ _ _)) heq
  have hsrc : readSrc s₂ (.mem (hdr (sArr aN))) = some (off B (slot w aN)) := by
    rw [readSrc_word (d := 8 * sArr aN) hs₂ (by simp only [State.ea, hdr, (k12.gpr (by decide)).trans hdi, hdrOff])
      (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega), hH₂.harr aN (by decide)]
  refine WP.seq (WP.mono (movMem_ok s₂ (dst := .r10) hsrc) fun s₃ ⟨h10, _, _, k₃⟩ => ?_)
  have k123 := k12.trans k₃.keep
  refine WP.mono (finish_ok (hs.congr k123.2.2) ((k123.gpr (by decide)).trans hdi)
    (k₃.2.1 ▸ hH₂) hZ hw1 hw h10 ho ho1 ho2 (by rw [k₃.2.1, hN₂]; exact hTlt))
    fun t ⟨hv, hf, kt⟩ => ?_
  rw [k₃.2.1, hN₂] at hv
  refine ⟨?_, ?_, ?_, (k123.trans kt).mono (by decide)⟩
  · rw [hv]; exact Nat.mod_lt _ hmpos
  · rw [hv, Nat.mod_mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx aTmp (by simp)
    have h3 := hx o (by simp)
    have hfin : t.mem x = s₃.mem x := hf x (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h1
      · exact h3)
    rw [hfin, k₃.2.1]
    exact ho12 x (by
      have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
      omega_using [h1, h2, hAT])

end VG.Proof.Bignum.X86_64.AdxSquare
