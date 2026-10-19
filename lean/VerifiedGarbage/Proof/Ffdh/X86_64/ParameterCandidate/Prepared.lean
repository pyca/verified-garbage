module

public import VerifiedGarbage.Proof.Bignum.ExternalWords
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Constants
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates on x86-64: a prepared shared Miller–Rabin modulus -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- All modulus-dependent data needed to call the shared round with any witness. -/
structure ModulusReady (s : State) (B : Addr) (Z w : Nat) (mi : BitVec 64) (N : Nat) : Prop where
  good : Good s B Z w mi
  inv : ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0
  n : wv s.mem B (slot w aN) w = N
  one : wv s.mem B (slot w aOne) w = 1
  r2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  r1 : wv s.mem B (slot w aR1) w = 2 ^ (64 * w) % N
  rm1 : wv s.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N
  exponent : ECtx s.mem B w N

def modulusRanges (w : Nat) : List (Nat × Nat) :=
  prepareRanges w ++ constantRanges w ++ [(slot w aE, 8 * (w + 1))]

theorem prepareModulus_ok (M : Mont) (R : R2Impl M) {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hd : MrDims B Z w)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (prepareModulus M.mm R.code) s fun t => ∃ mi', ModulusReady t B Z w mi' N ∧
      Frm B (modulusRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw : w < 2 ^ 31 := by have := hd.w128; omega
  have hz64 : Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left Z B.toNat) hg.scr.nowrap
  have hNread : slot w aN + 8 * w ≤ 2 ^ 64 := by
    have he := slot_le (w := w) (show aN < 8 by decide)
    omega_using [he, hd.z, hz64]
  have hNword : slot w aN + 8 ≤ 2 ^ 64 := by omega_using [hNread, hd.w4]
  have hOneread : slot w aOne + 8 * w ≤ 2 ^ 64 := by
    have he := slot_le (w := w) (show aOne < 8 by decide)
    omega_using [he, hd.z, hz64]
  have hR2read : slot w aR2 + 8 * w ≤ 2 ^ 64 := by
    have he := slot_le (w := w) (show aR2 < 8 by decide)
    omega_using [he, hd.z, hz64]
  have hR1read : slot w aR1 + 8 * w ≤ 2 ^ 64 := by
    have he := hd.x
    simp only [slot, aR1, aRm1] at he ⊢
    omega_using [he, hz64]
  have hRm1read : slot w aRm1 + 8 * w ≤ 2 ^ 64 := by omega_using [hd.x, hz64]
  unfold prepareModulus
  refine WP.seq (WP.mono (prepareR2_ok M R hg hd.z (by have := hd.w4; omega)
    (by have := hd.w128; omega) hn hodd hlo) fun u ⟨mi', hgu, hinv, hnu, hone, hr2, _, hf, ku⟩ => ?_)
  refine WP.seq (WP.mono (prepareConstants_ok M hgu hd.z hd.x (by have := hd.w4; omega) hw hnu hinv hone hodd hN1 hr2)
    fun v ⟨hgv, hr1, hrm1, hf', kv⟩ => ?_)
  have hnv : wv v.mem B (slot w aN) w = N := by
    rw [hf'.wv_eq (by simp only [constantRanges]; rng_disj) hNread]
    exact hnu
  have hinvv : ((word v.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf'.word_eq (by simp only [constantRanges]; rng_disj) hNword]
    exact hinv
  have hr2v : wv v.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [hf'.wv_eq (by simp only [constantRanges]; rng_disj) hR2read]
    exact hr2
  refine WP.mono (expSetup_ok hgv hd hnv hodd hN1) fun t ⟨he, hfe, hgt, kt⟩ => ?_
  refine ⟨mi', ⟨hgt, ?_, ?_, ?_, ?_, ?_, ?_, he⟩, (hf.append hf').append hfe,
    ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [hfe.word_eq (by rng_disj) hNword]; exact hinvv
  · rw [hfe.wv_eq (by rng_disj) hNread]; exact hnv
  · rw [hfe.wv_eq (by rng_disj) hOneread, hf'.wv_eq (by simp only [constantRanges]; rng_disj) hOneread]
    exact hone
  · rw [hfe.wv_eq (by rng_disj) hR2read]; exact hr2v
  · rw [hfe.wv_eq (by rng_disj) hR1read]; exact hr1
  · rw [hfe.wv_eq (by rng_disj) hRm1read]; exact hrm1

/-- A witness operation may change scratch arrays while retaining the modulus precomputation. -/
theorem ModulusReady.of_frm {s t : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    {rs : List (Nat × Nat)} {regs : List Reg} (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hf : Frm B rs s.mem t.mem) (k : Keep regs s t) (hdi : t.gpr .rdi = B)
    (hh : ∀ r ∈ rs, 128 ≤ r.1)
    (ha : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], ∀ r ∈ rs,
      slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j)
    (he : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE) :
    ModulusReady t B Z w mi N := by
  have hz64 : Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left Z B.toNat) h.good.scr.nowrap
  have hread : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], slot w j + 8 * w ≤ 2 ^ 64 := by
    intro j hj
    have hj' : j ≤ aRm1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    have hm := VG.Proof.Rsa.slot_mono (w := w) hj'
    omega_using [hm, hd.x, hz64]
  have hval : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], wv t.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun j hj => hf.wv_eq (ha j hj) (hread j hj)
  refine ⟨⟨h.good.scr.congr k.2.2, hdi, h.good.hdr.of_frm hf hh⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.word_eq (fun r hr => by have hd' := ha aN (by simp) r hr; omega_using [hd', hd.w4])
      (by have hb := hread aN (by simp); omega_using [hb, hd.w4])]
    exact h.inv
  · rw [hval aN (by simp)]; exact h.n
  · rw [hval aOne (by simp)]; exact h.one
  · rw [hval aR2 (by simp)]; exact h.r2
  · rw [hval aR1 (by simp)]; exact h.r1
  · rw [hval aRm1 (by simp)]; exact h.rm1
  · exact h.exponent.of_frm hf he (by
      have hb := aE_fits hd
      have hn := h.good.scr.nowrap
      omega_using [hb, hn])

/-- A write confined to an external byte buffer preserves workspace words. -/
theorem words_outside_bytes {B op : Addr} {Z len : Nat} {m m' : Mem}
    (hz : Z ≤ 2 ^ 64)
    (hf : ∀ a, (∀ i < len, a ≠ off op i) → m' a = m a)
    (hs : ∀ i < len, Z ≤ ofs B (off op i)) :
    ∀ d, d + 8 ≤ Z → word m' B d = word m B d :=
  VG.Proof.Bignum.words_outside_bytes hz hf hs

/-- Byte-buffer operations outside the workspace preserve every prepared word. -/
theorem ModulusReady.of_words {s t : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hm : ∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = B) : ModulusReady t B Z w mi N := by
  have hval : ∀ j, j ≤ aRm1 → wv t.mem B (slot w j) w = wv s.mem B (slot w j) w := by
    intro j hj
    have hs := VG.Proof.Rsa.slot_mono (w := w) hj
    exact wv_congr fun i hi => hm _ (by omega_using [hs, hd.x, hi])
  have hh : Hdr t.mem B w mi := by
    refine ⟨(hm _ (by have := hd.z; unfold slot hdrBytes at this; unfold sW; omega)).trans h.good.hdr.hw,
      (hm _ (by have := hd.z; unfold slot hdrBytes at this; unfold sMinv; omega)).trans h.good.hdr.hminv, ?_⟩
    intro j hj
    exact (hm _ (by have := hd.z; unfold slot hdrBytes sArr at *; omega)).trans (h.good.hdr.harr j hj)
  refine ⟨⟨h.good.scr.congr hwr, hdi, hh⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm _ (by have := slot_le (w := w) (show aN < 8 by decide); omega_using [this, hd.z, hd.w4])]
    exact h.inv
  · rw [hval aN (by decide)]; exact h.n
  · rw [hval aOne (by decide)]; exact h.one
  · rw [hval aR2 (by decide)]; exact h.r2
  · rw [hval aR1 (by decide)]; exact h.r1
  · rw [hval aRm1 (by decide)]; exact h.rm1
  · refine ⟨?_, ?_⟩
    · rw [hval aE (by decide)]; exact h.exponent.e
    · rw [hm _ (by have := aE_fits hd; omega)]
      exact h.exponent.l

end VG.Proof.Ffdh.X86_64.ParameterCandidate
