module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.TestsFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.MainShape
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Halve
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# An FFDH parameter candidate on PPC64LE: once `rand` is long enough

`main_ok`: p from the tape, its shape (the congruence, the sieves of p and
q, q's parity), and the tests, against `checkedCandidate`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkedCandidate checked_eq testsSpec)

/-- `Ph` survives a change of memory that keeps the header but `hBad`. -/
theorem Ph.keepBad {p : PP} {mb : Nat} {s t : State} (h : Ph p mb s)
    (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11) (r29 : t.gpr .r29 = s.gpr .r29)
    (hw : ∀ d, d + 8 ≤ 200 ∨ (208 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d) : Ph p mb t :=
  ⟨r10.trans h.r10, r11.trans h.r11, r29.trans h.r29, (hw 248 (by decide)).trans h.mbW,
    (hw 216 (by decide)).trans h.kW, (hw 48 (by decide)).trans h.wW, (hw 224 (by decide)).trans h.strideW,
    fun j hj => (hw _ (by omega)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW,
    (hw 192 (by decide)).trans h.topW⟩

/-- A piece of the shape checks, which changes `hBad` and array 0 at most. -/
theorem shapeStep {p : PP} {s t : State} (h : St p s) (hp : Ph p p.bits s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 p.L) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r = (200, 8) ∨ r = (256, 8 * wOf p.bits)) {regs : List Reg} (k : Keep regs s t)
    (h10 : Reg.r10 ∉ regs) (h11 : Reg.r11 ∉ regs) (h29 : Reg.r29 ∉ regs) (h31 : Reg.r31 ∉ regs)
    (h2 : Reg.r2 ∉ regs := by decide) :
    St p t ∧ Ph p p.bits t ∧ word t.mem p.B 152 = BitVec.ofNat 64 p.L := by
  have hdn := h.dims.n
  have hb2 := h.dims.b2
  have hb1 := h.dims.b1
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hw : wOf p.bits = (p.bits + 63) / 64 := rfl
  have st := h.step (Frm.toMut hf fun r hr' => by
    rcases hr r hr' with rfl | rfl
    · exact InMut.hdr (i := 25) (by decide)
    · exact InMut.arrays (by omega) (by simp only [saveBytes]; omega)) k h31 h2
  have wd : ∀ d, d + 8 ≤ 200 ∨ (208 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr' => by rcases hr r hr' with rfl | rfl <;> dsimp only <;> omega) (by omega)
  exact ⟨st, hp.keepBad (k.gpr _ h10) (k.gpr _ h11) (k.gpr _ h29) wd, (wd 152 (by decide)).trans hu⟩

/-- `hBad` into `r5`. -/
theorem badLoad_ok {p : PP} {s : State} (h : St p s) :
    WP isa (.block [ldh .r5 hBad]) s fun t => t.gpr .r5 = word s.mem p.B 200 ∧ t.mem = s.mem ∧ Keep [.r5] s t := by
  have l200 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 200) 8 := h.ld (d := 200) (by decide)
  exact WP.mono (WP.keep [.r5] (Q := fun t => t.gpr .r5 = word s.mem p.B 200 ∧ t.mem = s.mem)
    (by simp only [ldh, hBad]; prun [h.r31, l200]) (by decide)) fun t ⟨⟨t5, tm⟩, k⟩ => ⟨t5, tm, k⟩

/-- `main`: p, its shape, and the tests. -/
theorem main_ok (R : RoundImpl) {p : PP} {s : State} (h : St p s)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (main R.name R.code) s (CEnd p (checkedCandidate p.bits p.g p.r)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  rw [checked_eq hL]
  generalize hc : Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take ((p.bits + 7) / 8))) = c
  have hc' : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) := hc.symm
  have hsh := shape_iff (x := Spec.Rsa.os2ip (p.r.take p.L)) hb1 hb2 h.dims.g
  obtain ⟨ho, hl, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc'] at hsh ho hl hcu
  -- A rejected shape.
  have reject : ∀ {t : State}, St p t → word t.mem p.B 152 = BitVec.ofNat 64 p.L →
      (Spec.Ffdh.generationShape p.bits p.g c && Spec.Ffdh.primeShape c &&
        Spec.Ffdh.primeShape ((c - 1) / 2)) = false →
      WP isa (.block (finish 2)) t (CEnd p (if !(Spec.Ffdh.generationShape p.bits p.g c &&
        Spec.Ffdh.primeShape c && Spec.Ffdh.primeShape ((c - 1) / 2)) then some (none, p.r.drop p.L)
        else testsSpec c (p.r.drop p.L))) := fun st hu hf => by
    rw [hf]
    simp only [Bool.not_false, ↓reduceIte]
    refine finEnd st (r := 2) (v := p.L) (Or.inr rfl) rfl rfl ?_ hu
    simp only [usedOf, List.length_drop, Nat.reduceEqDiff, ↓reduceIte]
    omega
  unfold main
  -- p's working space.
  refine WP.seq (WP.mono (phase_ok h false) fun t₁ ⟨⟨st₁, ph₁, hf₁⟩, _⟩ => ?_)
  simp only [mbOf, Bool.false_eq_true, ↓reduceIte] at ph₁
  have hU₁ : word t₁.mem p.B 152 = BitVec.ofNat 64 p.L := by rw [hf₁.word_eq phR_used (by decide)]; exact hU
  -- p.
  refine WP.seq (WP.mono (shapeP_ok st₁ ph₁ hL) fun t₂ ⟨⟨hn₂, f₂⟩, k₂⟩ => ?_)
  rw [← hc'] at hn₂
  obtain ⟨st₂, ph₂, hU₂⟩ := shapeStep st₁ ph₁ hU₁ f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr, hsl]; exact .inr rfl) k₂ (by decide) (by decide) (by decide) (by decide)
  -- Its congruence.
  refine WP.seq (WP.mono (residue_ok st₂ ph₂) fun t₃ ⟨⟨hb₃, f₃⟩, k₃⟩ => ?_)
  rw [hn₂] at hb₃
  have hn₃ : wv t₃.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = c := by
    rw [f₃.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, hsl]; exact .inr (by decide)) (by omega)]; exact hn₂
  obtain ⟨st₃, ph₃, hU₃⟩ := shapeStep st₂ ph₂ hU₂ f₃ (fun r hr => .inl (List.mem_singleton.mp hr)) k₃
    (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (badLoad_ok st₃) fun t₄ ⟨t5, tm₄, k₄⟩ => ?_)
  obtain ⟨st₄, ph₄, hU₄⟩ := shapeStep st₃ ph₃ hU₃ (rs := []) (by rw [tm₄]; exact Frm.refl _ _ _) (by simp) k₄
    (by decide) (by decide) (by decide) (by decide)
  refine WP.ite (word t₃.mem p.B 200 == 0) (by rw [eval_zero, t5]) (fun hz => ?_) (fun hz => ?_)
  rotate_left
  · -- The congruence fails.
    refine reject st₄ hU₄ (Bool.eq_false_iff.mpr fun ht => ?_)
    have h0 : word t₃.mem p.B 200 = 0#64 := hb₃.mpr (hsh.mpr ht).1
    simp [h0] at hz
  have hz₃ : word t₃.mem p.B 200 = 0#64 := beq_iff_eq.mp hz
  have hn₄ : wv t₄.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = c := by rw [tm₄]; exact hn₃
  have hw8 : 8 ≤ wOf p.bits := by omega
  have hw128 : wOf p.bits ≤ 128 := by omega
  have hZw : slot (wOf p.bits) 0 + 8 * wOf p.bits ≤ p.Z := by rw [hsl]; omega
  -- The sieve of p.
  refine WP.seq (WP.mono (sieve_ok oddPrimes256 (by decide) st₄.scr st₄.r31 ph₄.r10 ph₄.r11 hn₄ (by omega)
    (by omega) hZw (by omega)) fun t₅ ⟨⟨hb₅, f₅⟩, k₅⟩ => ?_)
  have hn₅ : wv t₅.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = c := by
    rw [f₅.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, hsl]; exact .inr (by decide)) (by omega)]; exact hn₄
  obtain ⟨st₅, ph₅, hU₅⟩ := shapeStep st₄ ph₄ hU₄ f₅ (fun r hr => .inl (List.mem_singleton.mp hr)) k₅
    (by decide) (by decide) (by decide) (by decide)
  -- q.
  refine WP.seq (WP.mono (halveQ_ok st₅ ph₅.r10 ph₅.r11 hn₅ (by omega) (by omega) hZw) fun t₆ ⟨⟨hn₆, hb₆, f₆⟩, k₆⟩ => ?_)
  obtain ⟨st₆, ph₆, hU₆⟩ := shapeStep st₅ ph₅ hU₅ f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hsl]; exact .inr rfl
    · exact .inl rfl) k₆ (by decide) (by decide) (by decide) (by decide)
  -- The sieve of q.
  refine WP.seq (WP.mono (sieve_ok oddPrimes256 (by decide) st₆.scr st₆.r31 ph₆.r10 ph₆.r11 hn₆ (by omega)
    (by omega) hZw (by omega)) fun t₇ ⟨⟨hb₇, f₇⟩, k₇⟩ => ?_)
  have hn₇ : wv t₇.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = c / 2 := by
    rw [f₇.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, hsl]; exact .inr (by decide)) (by omega)]; exact hn₆
  obtain ⟨st₇, ph₇, hU₇⟩ := shapeStep st₆ ph₆ hU₆ f₇ (fun r hr => .inl (List.mem_singleton.mp hr)) k₇
    (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (badLoad_ok st₇) fun t₈ ⟨t5', tm₈, k₈⟩ => ?_)
  obtain ⟨st₈, ph₈, hU₈⟩ := shapeStep st₇ ph₇ hU₇ (rs := []) (by rw [tm₈]; exact Frm.refl _ _ _) (by simp) k₈
    (by decide) (by decide) (by decide) (by decide)
  have hall : word t₇.mem p.B (8 * hBad) = 0#64 ↔
      goodRes p.g c ∧ (∀ d ∈ oddPrimes256, c % d ≠ 0) ∧ c / 2 % 2 = 1 ∧ ∀ d ∈ oddPrimes256, c / 2 % d ≠ 0 := by
    rw [hb₇, hb₆, hb₅]
    have : word t₄.mem p.B (8 * hBad) = 0#64 ↔ goodRes p.g c := by rw [tm₄]; exact hb₃
    rw [this]
    exact ⟨fun ⟨⟨⟨a, b⟩, c'⟩, d⟩ => ⟨a, b, c', d⟩, fun ⟨a, b, c', d⟩ => ⟨⟨⟨a, b⟩, c'⟩, d⟩⟩
  refine WP.ite (word t₇.mem p.B 200 == 0) (by rw [eval_zero, t5']) (fun hz' => ?_) (fun hz' => ?_)
  · -- The shape passes: the tests.
    have hshape := hsh.mp (hall.mp (beq_iff_eq.mp hz'))
    rw [hshape]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hq : (c - 1) / 2 = c / 2 := by omega
    obtain ⟨_, _, hqo, _⟩ := hall.mp (beq_iff_eq.mp hz')
    rw [hc'] at hq hqo ⊢
    refine tests_ok R st₈ rfl ?_ (by rw [hq]; exact hqo) hU₈ hL
    rw [hq, ← hc', tm₈]; exact hn₇
  · refine reject st₈ hU₈ (Bool.eq_false_iff.mpr fun ht => ?_)
    have h0 : word t₇.mem p.B 200 = 0#64 := hall.mpr (hsh.mpr ht)
    simp [h0] at hz'

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
