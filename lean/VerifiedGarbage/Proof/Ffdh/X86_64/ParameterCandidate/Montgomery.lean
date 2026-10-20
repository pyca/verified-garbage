module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # FFDH parameter candidates on x86-64: precompute R² at the candidate's own width -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def prepareRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sMinv, 8), (slot w aOne, 8 * (w + 2))] ++ r2Ranges w

theorem prepareR2_ok (M : Mont) (R : R2Impl M) {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (prepareR2 R.code) s fun t => ∃ mi', Good t B Z w mi' ∧
      ((word t.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aN) w = N ∧ wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aR2) w < N ∧ Frm B (prepareRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw31 : w < 2 ^ 31 := by omega
  have hnw := hg.scr.nowrap
  have hN8 := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hO8 := Nat.le_trans (slot_le (w := w) (show aOne < 8 by decide)) hZ
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := w) _ _ _ (by omega), hn, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
    exact hodd
  unfold prepareR2
  simp only [seqs]
  refine WP.seq (WP.mono (msHead_ok hg hZ hodd0) fun s₁ ⟨hg₁, hinv₁, hdx₁, hcx₁, h12₁, hm₁, k₁⟩ => ?_)
  generalize hmi : s₁.gpr .r15 = mi' at hg₁ hinv₁ hm₁
  have hn₁ : wv s₁.mem B (slot w aN) w = N := by
    rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega)]; exact hn
  have hw0₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hm₁, hdrStore_word _ _ _ (by decide) (by decide) (by omega)]
  refine WP.seq (WP.mono (setWord_ok hg₁.scr hg₁.rdi hg₁.hdr hZ h12₁ (by omega) hw31 (o := aOne) (by decide) (ri := .rcx)
    (by decide) (i := 0) (by omega) hcx₁) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  rw [hdx₁] at hv₂
  have ha₂ : Arrays B w [aOne] s₁.mem s₂.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₂ (Nat.le_refl _) (Nat.le_refl _)
  have hg₂ : Good s₂ B Z w mi' := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, ha₂.hdr hg₁.hdr⟩
  have hn₂ : wv s₂.mem B (slot w aN) w = N := by rw [ha₂.wv_of_not_mem (by decide) (by decide) (by omega)]; exact hn₁
  have hw0₂ : word s₂.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₂.word0_of_not_mem (by decide) (by decide) (by omega) (by omega)]; exact hw0₁
  have hl : InRegions (s₂.rd ++ s₂.wr) (off B (8 * sArr aN)) 8 :=
    hg₂.scr.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega)
  refine WP.seq (WP.mono (WP.keep [.r10] (Q := fun u => u.gpr .r10 = off B (slot w aN) ∧ u.mem = s₂.mem)
    (by xrun [State.ea, hdr, hg₂.rdi, hdrOff, hl, hg₂.hdr.harr aN (by decide)]) rfl)
    fun u ⟨⟨h10, hm⟩, k⟩ => ?_)
  have hgu : Good u B Z w mi' := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi,
    by rw [hm]; exact hg₂.hdr⟩
  refine WP.mono (R.ok hgu hZ hw hw' (by rw [hm]; exact hn₂)
    (by rw [hm, hw0₂]; exact hinv₁) ((k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12₁))
    h10 hodd hlo) fun t ⟨hgt, hlt, hr, hf, kk⟩ => ?_
  have hf' : Frm B (r2Ranges w) s₂.mem t.mem := by rw [hm] at hf; exact hf
  have hN : wv t.mem B (slot w aN) w = N := by
    rw [hf'.wv_eq (fun r hr => by have := r2Ranges_arr w (j := aN) (by decide) (by decide) (by decide) r hr; omega) (by omega)]
    exact hn₂
  have h0 : word t.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hf'.word_eq (fun r hr => by have := r2Ranges_arr w (j := aN) (by decide) (by decide) (by decide) r hr; omega) (by omega)]
    exact hw0₂
  have h1 : wv t.mem B (slot w aOne) w = 1 := by
    rw [hf'.wv_eq (fun r hr => by have := r2Ranges_arr w (j := aOne) (by decide) (by decide) (by decide) r hr; omega) (by omega), hv₂]
    rfl
  refine ⟨mi', hgt, by rw [h0]; exact hinv₁, hN, h1, ?_, hlt, ?_,
    (((k₁.trans k₂).trans k).trans kk).mono (by decide)⟩
  · rw [← Nat.mod_eq_of_lt hlt]
    exact hr
  · have f₁ : Frm B [(8 * sMinv, 8)] s.mem s₁.mem := by
      rw [hm₁]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
    have f₂ : Frm B [(slot w aOne, 8 * (w + 2))] s₁.mem s₂.mem := Frm.of_outside ho₂ (by simp)
    exact (f₁.append f₂).append hf'

end VG.Proof.Ffdh.X86_64.ParameterCandidate
