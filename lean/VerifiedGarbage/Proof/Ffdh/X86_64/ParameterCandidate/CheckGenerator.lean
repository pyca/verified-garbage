module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: generator policy at the p phase

The check accepts p only if, besides the generator's congruence, neither 3,
5 nor 7 divides p or q = (p − 1)/2 (and q is odd), all of which the trial
division of p and q that follows would reject: `congruent_sieved`. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- What the generator check accepts: the generator's congruence (`screen`
implies it) and `screen`. -/
def CandidateP.congruent (p : CandidateP) : Bool :=
  Spec.Ffdh.generationShape p.bits p.gen p.P && screen p.gen p.P

private theorem fin2 : ∀ r < 840, r % 2 = 1 ∧ r % 24 = 11 ∧ r % 5 ≠ 0 ∧ r % 7 ≠ 0 ∧
    (r - 1) / 2 % 5 ≠ 0 ∧ (r - 1) / 2 % 7 ≠ 0 → r ∈ allowed2 := by decide +kernel

private theorem fin5 : ∀ r < 420, r % 2 = 1 ∧ (r % 10 = 3 ∨ r % 10 = 7) ∧ r % 3 ≠ 0 ∧ r % 7 ≠ 0 ∧
    (r - 1) / 2 % 2 = 1 ∧ (r - 1) / 2 % 3 ≠ 0 ∧ (r - 1) / 2 % 7 ≠ 0 → r ∈ allowed5 := by
  decide +kernel

private theorem tab012 : VG.Impl.RsaKeyGen.tabEntry 0 = 3 ∧ VG.Impl.RsaKeyGen.tabEntry 1 = 5 ∧
    VG.Impl.RsaKeyGen.tabEntry 2 = 7 := by
  unfold VG.Impl.RsaKeyGen.tabEntry VG.Impl.RsaKeyGen.slots
  rw [VG.Impl.RsaKeyGen.primes.lit_eq]
  exact ⟨rfl, rfl, rfl⟩

private theorem small_of_primeShape {v : Nat} (hv : 8161 < v) (ho : v % 2 = 1)
    (h : Spec.Ffdh.primeShape v = true) : v % 3 ≠ 0 ∧ v % 5 ≠ 0 ∧ v % 7 ≠ 0 := by
  rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve hv ho] at h
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, List.mem_range, beq_iff_eq] at h
  obtain ⟨h3, h5, h7⟩ := tab012
  exact ⟨by simpa only [h3] using h 0 (by decide), by simpa only [h5] using h 1 (by decide),
    by simpa only [h7] using h 2 (by decide)⟩

private theorem odd_of_primeShape {v : Nat} (h : Spec.Ffdh.primeShape v = true) : v % 2 = 1 := by
  unfold Spec.Ffdh.primeShape at h
  exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2

private theorem half840 {P : Nat} (h : P % 2 = 1) :
    (P % 840 - 1) / 2 % 5 = (P - 1) / 2 % 5 ∧ (P % 840 - 1) / 2 % 7 = (P - 1) / 2 % 7 := by
  omega

private theorem half420 {P : Nat} (h : P % 2 = 1) :
    (P % 420 - 1) / 2 % 2 = (P - 1) / 2 % 2 ∧ (P % 420 - 1) / 2 % 3 = (P - 1) / 2 % 3 ∧
      (P % 420 - 1) / 2 % 7 = (P - 1) / 2 % 7 := by
  omega

/-- A candidate with the generator's congruence whose p and q have the
sieved shape passes `screen`. -/
theorem screen_of_shape {bits generator P : Nat} (hgen : generator = 2 ∨ generator = 5)
    (hodd : P % 2 = 1) (hP : 8161 < P) (hQ : 8161 < (P - 1) / 2)
    (hs : Spec.Ffdh.generationShape bits generator P = true)
    (hp : Spec.Ffdh.primeShape P = true) (hq : Spec.Ffdh.primeShape ((P - 1) / 2) = true) :
    screen generator P = true := by
  obtain ⟨p3, p5, p7⟩ := small_of_primeShape hP hodd hp
  have qodd := odd_of_primeShape hq
  obtain ⟨q3, q5, q7⟩ := small_of_primeShape hQ qodd hq
  have mm := fun (m k : Nat) (h : k ∣ m) => Nat.mod_mod_of_dvd P h
  rcases hgen with rfl | rfl
  · have h24 : P % 24 = 11 := by
      unfold Spec.Ffdh.generationShape at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ite_true] at hs
      exact hs.2
    have hr : P % 840 < 840 := Nat.mod_lt _ (by decide)
    have hscreen : screen 2 P = decide (P % 840 ∈ allowed2) := ite_eq_left_of_eq_true _ _ (eq_true rfl)
    rw [hscreen]
    obtain ⟨e5, e7⟩ := half840 hodd
    exact decide_eq_true <| fin2 (P % 840) hr ⟨(mm 840 2 (by decide)).trans hodd,
      (mm 840 24 (by decide)).trans h24, (mm 840 5 (by decide)).symm ▸ p5,
      (mm 840 7 (by decide)).symm ▸ p7, e5 ▸ q5, e7 ▸ q7⟩
  · have h10 : P % 10 = 3 ∨ P % 10 = 7 := by
      unfold Spec.Ffdh.generationShape at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
        show ((5 : Nat) == 2) = false from rfl, Bool.false_eq_true, ite_false, true_and] at hs
      exact hs.2
    have hr : P % 420 < 420 := Nat.mod_lt _ (by decide)
    have hscreen : screen 5 P = decide (P % 420 ∈ allowed5) := ite_eq_right_of_eq_false _ _ (eq_false (by decide))
    rw [hscreen]
    obtain ⟨e2, e3, e7⟩ := half420 hodd
    exact decide_eq_true <| fin5 (P % 420) hr ⟨(mm 420 2 (by decide)).trans hodd,
      (mm 420 10 (by decide)).symm ▸ h10, (mm 420 3 (by decide)).symm ▸ p3,
      (mm 420 7 (by decide)).symm ▸ p7, e2.trans qodd, e3 ▸ q3, e7 ▸ q7⟩

/-- Rejecting by `screen` before the sieve rejects nothing the sieve accepts. -/
theorem congruent_sieved {p : CandidateP} (hb : 512 ≤ p.bits) (hgen : p.gen = 2 ∨ p.gen = 5) :
    ((p.congruent && p.sieved p.P) && p.sieved p.Q) =
      ((Spec.Ffdh.generationShape p.bits p.gen p.P && p.sieved p.P) && p.sieved p.Q) := by
  obtain ⟨hodd, hl, hu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega)
    (Spec.Rsa.os2ip p.prefix)
  obtain ⟨hql, -⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega) hodd hl hu
  have h13 : 2 ^ 13 ≤ 2 ^ (p.bits - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have h14 : 2 ^ 13 ≤ 2 ^ (p.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  change p.P % 2 = 1 at hodd
  change 2 ^ (p.bits - 1) ≤ p.P at hl
  change 2 ^ (p.bits - 2) ≤ (p.P - 1) / 2 at hql
  unfold CandidateP.congruent
  cases hs : Spec.Ffdh.generationShape p.bits p.gen p.P <;>
    cases hsp : p.sieved p.P <;> cases hsq : p.sieved p.Q <;> simp only [Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true]
  unfold CandidateP.sieved at hsp hsq
  exact screen_of_shape hgen hodd (by omega) (by unfold CandidateP.Q at hsq; omega) hs
    ((Bool.and_eq_true _ _).mp hsp).1 ((Bool.and_eq_true _ _).mp hsq).1

theorem generatorCheck_state_ok {p : CandidateP} {used : Nat} {c : Checks} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords false) mi)
    (hp : PhaseHeader p false c s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords false) aN) (p.phaseWords false) = p.P) :
    WP isa (.seq (.block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax oGen))]) generatorCheck) s
      fun t => CandidateTape p used t ∧
        Good t (off p.B 256) (p.Z - 256) (p.phaseWords false) mi ∧ PhaseHeader p false c t ∧
        wv t.mem (off p.B 256) (slot (p.phaseWords false) aN) (p.phaseWords false) = p.P ∧
        t.zf = some p.congruent ∧
        t.mem = s.mem ∧ Keep mmRegs s t := by
  have hgen := h.base.hdr (oGen, BitVec.ofNat 64 p.gen) (by simp [CandidateP.headers])
  have hrd := h.base.scr.ld (show 8 * oGen + 8 ≤ p.Z by
    change 88 ≤ p.Z
    omega_using [h.base.header_room])
  have hlinkrd := hg.scr.ld (show 8 * sLink + 8 ≤ p.Z - 256 by
    have hz := (h.base.phase_dims false).z
    change 136 ≤ p.Z - 256
    unfold slot hdrBytes at hz
    omega)
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx] (Q := fun u =>
    u.gpr .rdx = BitVec.ofNat 64 p.gen ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, ws, hg.rdi, hdrOff, hp.link, hgen, hrd, hlinkrd]) rfl)
    fun u ⟨⟨hdx, hm⟩, ku⟩ => ?_)
  have hgu : Good u (off p.B 256) (p.Z - 256) (p.phaseWords false) mi :=
    ⟨hg.scr.congr ku.2.2, (ku.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  have hbit : Spec.RsaKeyGen.bitLength p.P = p.bits :=
    VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_using [h.base.bits1]) _ |>.1
  refine WP.mono (generatorCheck_ok hgu (h.base.phase_dims false).z
    (by omega_using [(h.base.phase_room false).1]) (by omega_using [(h.base.phase_room false).2.1])
    h.base.bits1 h.base.bits2 (by rw [hm, hn]; exact hbit) h.base.gen hdx)
    fun t ⟨hz, hmt, kt⟩ => ?_
  have hmem : t.mem = s.mem := hmt.trans hm
  have kk : Keep mmRegs s t := (ku.trans kt).mono (by decide)
  have hf : CandidateFrame p s.mem t.mem := by rw [hmem]; exact CandidateFrame.refl _ _
  have hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) := fun _ _ => by rw [hmem]
  refine ⟨h.keep hf hh kk ((kk.gpr (by decide)).trans h.base.sp),
    ⟨hg.scr.congr kk.2.2, (kk.gpr (by decide)).trans hg.rdi, by rw [hmem]; exact hg.hdr⟩,
    ⟨by rw [hmem]; exact hp.bits, by rw [hmem]; exact hp.len,
      by rw [hmem]; exact hp.checks, by rw [hmem]; exact hp.link⟩, by simpa only [hmem] using hn,
    by simpa only [hm, hn, CandidateP.congruent] using hz, hmem, kk⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
