module

import VerifiedGarbage.Proof.Bignum.ExternalWords
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-! ### `Ffdh.X86_64.ParameterCandidate.Constants`, which this module and modules that import it used -/

section

/-! # FFDH parameter candidates on x86-64: Montgomery encodings of 1 and −1 -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def constantRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (slot w aR1, 8 * w), (slot w aRm1, 8 * w)]

theorem prepareConstants_ok (M : Mont) {s₃ : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s₃ B Z w mi) (hZ : slot w 8 ≤ Z) (hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hn : wv s₃.mem B (slot w aN) w = N)
    (hinv : ((word s₃.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s₃.mem B (slot w aOne) w = 1) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hr2 : wv s₃.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N) :
    WP isa (prepareConstants M.mm) s₃ fun t => Good t B Z w mi ∧
      wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N ∧
      Frm B (constantRanges w) s₃.mem t.mem ∧ Keep mmRegs s₃ t := by
  have hR : Nat.Coprime (2 ^ (64 * w)) N := coprime_pow2 hodd _
  have hnw := hg.scr.nowrap
  have hR1Z : slot w aR1 + 8 * (w + 2) ≤ Z :=
    Nat.le_trans (Nat.add_le_add_right (VG.Proof.Rsa.slot_mono (w := w) (by decide : aR1 ≤ aRm1)) _) hXZ
  have hR1readZ : slot w aR1 + 8 * w ≤ Z :=
    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 8 (Nat.le_add_right w 2)) _) hR1Z
  have hR1read : slot w aR1 + 8 * w ≤ 2 ^ 64 :=
    Nat.le_trans hR1readZ (Nat.le_trans (Nat.le_add_left Z B.toNat) hnw)
  unfold prepareConstants copyR1 negateR1
  -- `R mod c`.
  refine WP.seq (WP.mono (M.mm_ok hg hZ (by omega_using [hw]) hw' (o := aY) (a := aR2) (b := aOne) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hinv
    (by rw [hone, hn]; exact hN1)) fun s₄ ⟨hg₄, hlt₄, hy₄, ha₄, k₄⟩ => ?_)
  rw [hn, hr2, hone] at hy₄
  rw [hn] at hlt₄
  have hY : wv s₄.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt₄]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy₄, Nat.mul_one, Nat.mod_mod]
  have hn₄ : wv s₄.mem B (slot w aN) w = N := by rw [ha₄.wv_of_not_mem (by decide) (by decide) (by omega_using [hZ, hnw])]; exact hn
  -- `[aR1] := R mod c`.
  refine WP.seq (WP.mono (copyToExt_ok hg₄ hZ (by omega_using [hw]) hw' (a := aY) (d := aR1) (by decide) (by decide)
    hR1Z) fun s₅ ⟨hv₅, ho₅, k₅⟩ => ?_)
  rw [hY] at hv₅
  have hg₅ : Good s₅ B Z w mi := ⟨hg₄.scr.congr k₅.2.2, (k₅.gpr (by decide)).trans hg₄.rdi,
    Hdr.outside hg₄.hdr ho₅ (by unfold slot; omega_using [])⟩
  have hout5 : ∀ {j : Nat}, j < 8 → wv s₅.mem B (slot w j) w = wv s₄.mem B (slot w j) w := fun {j} hj =>
    ho₅.wv (Or.inl (by have := slot_le (w := w) hj; have : slot w 8 ≤ slot w aR1 := (by unfold slot aR1; omega_using []); omega_arith))
      (by have := slot_le (w := w) hj; omega_using [hZ, hnw, this])
  -- `[aRm1] := c − R mod c`.
  refine WP.mono (msRm1_ok hg₅ hZ hXZ (by omega_using [hw]) hw' (by rw [hv₅, hout5 (by decide), hn₄]; exact Nat.mod_lt _ (by omega_using [hodd])))
    fun s₆ ⟨hv₆, ho₆, k₆⟩ => ?_
  rw [hv₅, hout5 (by decide), hn₄] at hv₆
  have hg₆ : Good s₆ B Z w mi := ⟨hg₅.scr.congr k₆.2.2, (k₆.gpr (by decide)).trans hg₅.rdi,
    Hdr.outside hg₅.hdr ho₆ (by unfold slot; omega_using [])⟩
  refine ⟨hg₆, ?_, hv₆, ?_, ((k₄.trans k₅).trans k₆).mono (by decide)⟩
  · rw [ho₆.wv (Or.inl (by unfold slot aRm1 aR1; omega_using [])) hR1read]
    exact hv₅
  · have f₄ : Frm B (constantRanges w) s₃.mem s₄.mem := Frm.of_arrays ha₄ (by simp [constantRanges])
    have f₅ : Frm B (constantRanges w) s₄.mem s₅.mem := Frm.of_outside ho₅ (by simp [constantRanges])
    have f₆ : Frm B (constantRanges w) s₅.mem s₆.mem := Frm.of_outside ho₆ (by simp [constantRanges])
    exact (f₄.trans f₅).trans f₆

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

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
  have hw : w < 2 ^ 31 := by have := hd.w128; omega_arith
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
  refine WP.seq (WP.mono (prepareR2_ok M R hg hd.z (by have := hd.w4; omega_arith)
    (by have := hd.w128; omega_arith) hn hodd hlo) fun u ⟨mi', hgu, hinv, hnu, hone, hr2, _, hf, ku⟩ => ?_)
  refine WP.seq (WP.mono (prepareConstants_ok M hgu hd.z hd.x (by have := hd.w4; omega_arith) hw hnu hinv hone hodd hN1 hr2)
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
    refine ⟨(hm _ (by have := hd.z; unfold slot hdrBytes at this; unfold sW; omega_arith)).trans h.good.hdr.hw,
      (hm _ (by have := hd.z; unfold slot hdrBytes at this; unfold sMinv; omega_arith)).trans h.good.hdr.hminv, ?_⟩
    intro j hj
    exact (hm _ (by have := hd.z; unfold slot hdrBytes sArr at *; omega_arith)).trans (h.good.hdr.harr j hj)
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
    · rw [hm _ (by have := aE_fits hd; omega_arith)]
      exact h.exponent.l

end VG.Proof.Ffdh.X86_64.ParameterCandidate
