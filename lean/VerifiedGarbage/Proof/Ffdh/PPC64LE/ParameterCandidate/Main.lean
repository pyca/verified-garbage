module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.TestsFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.MainShape
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Halve
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
    fun j hj => (hw _ (by omega_arith)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW,
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
    · exact InMut.arrays (by omega_arith) (by simp only [saveBytes]; omega_arith)) k h31 h2
  have wd : ∀ d, d + 8 ≤ 200 ∨ (208 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr' => by rcases hr r hr' with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  exact ⟨st, hp.keepBad (k.gpr _ h10) (k.gpr _ h11) (k.gpr _ h29) wd, (wd 152 (by decide)).trans hu⟩

/-- `hBad` into `r5`. -/
theorem badLoad_ok {p : PP} {s : State} (h : St p s) :
    WP isa (.block [ldh .r5 hBad]) s fun t => t.gpr .r5 = word s.mem p.B 200 ∧ t.mem = s.mem ∧ Keep [.r5] s t := by
  have l200 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 200) 8 := h.ld (d := 200) (by decide)
  exact WP.mono (WP.keep [.r5] (Q := fun t => t.gpr .r5 = word s.mem p.B 200 ∧ t.mem = s.mem)
    (by simp only [ldh, hBad]; prun [h.r31, l200]) (by decide)) fun t ⟨⟨t5, tm⟩, k⟩ => ⟨t5, tm, k⟩

instance (g x : Nat) : Decidable (goodRes g x) := by unfold goodRes; infer_instance

/-- In p's working space, with `x` in array 0 and `hBad` zero iff `B`. -/
structure MB (p : PP) (x : Nat) (B : Prop) (t : State) : Prop where
  st : St p t
  ph : Ph p p.bits t
  u : word t.mem p.B 152 = BitVec.ofNat 64 p.L
  n : wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = x
  bad : word t.mem p.B (8 * hBad) = 0#64 ↔ B

/-- p's working space, and p. -/
theorem mainA_ok {p : PP} {s : State} (h : St p s) (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L)
    (hL : p.L ≤ p.r.length) :
    WP isa (.seq (phase false) shapeP) s fun t => St p t ∧ Ph p p.bits t ∧ word t.mem p.B 152 = BitVec.ofNat 64 p.L ∧
      wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) =
        Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) := by
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  refine WP.seq (WP.mono (phase_ok h false) fun t₁ ⟨⟨st₁, ph₁, hf₁⟩, _⟩ => ?_)
  simp only [mbOf, Bool.false_eq_true, ↓reduceIte] at ph₁
  have hU₁ : word t₁.mem p.B 152 = BitVec.ofNat 64 p.L := by rw [hf₁.word_eq phR_used (by decide)]; exact hU
  refine WP.mono (shapeP_ok st₁ ph₁ hL) fun t₂ ⟨⟨hn₂, f₂⟩, k₂⟩ => ?_
  obtain ⟨st₂, ph₂, hU₂⟩ := shapeStep st₁ ph₁ hU₁ f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr, hsl]; exact .inr rfl) k₂ (by decide) (by decide) (by decide) (by decide)
  exact ⟨st₂, ph₂, hU₂, hn₂⟩

/-- p's congruence. -/
theorem residue_mb {p : PP} {s : State} {x : Nat} (h : St p s) (hp : Ph p p.bits s)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hn : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = x) :
    WP isa residue s (MB p x (goodRes p.g x)) := by
  have hdn := h.dims.n
  have hb2 := h.dims.b2
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  refine WP.mono (residue_ok h hp) fun t ⟨⟨hb, f⟩, k⟩ => ?_
  rw [hn] at hb
  obtain ⟨st, ph, hU'⟩ := shapeStep h hp hU f (fun r hr => .inl (List.mem_singleton.mp hr)) k
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨st, ph, hU', ?_, hb⟩
  rw [f.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, hsl]; exact .inr (by decide)) (by omega_arith)]; exact hn

/-- `hBad` into `r5`. -/
theorem MB.badLoad {p : PP} {x : Nat} {B : Prop} {s : State} (h : MB p x B s) :
    WP isa (.block [ldh .r5 hBad]) s fun t => MB p x B t ∧ t.gpr .r5 = word s.mem p.B 200 := by
  refine WP.mono (badLoad_ok h.st) fun t ⟨t5, tm, k⟩ => ?_
  obtain ⟨st, ph, hU⟩ := shapeStep h.st h.ph h.u (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨⟨st, ph, hU, by rw [tm]; exact h.n, by rw [tm]; exact h.bad⟩, t5⟩

/-- A sieve of array 0. -/
theorem MB.sieve {p : PP} {x : Nat} {B : Prop} {s : State} (h : MB p x B s) :
    WP isa VG.Impl.Ffdh.PPC64LE.ParameterCandidate.sieve s (MB p x (B ∧ ∀ d ∈ oddPrimes256, x % d ≠ 0)) := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hdn := h.st.dims.n
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hZw : slot (wOf p.bits) 0 + 8 * wOf p.bits ≤ p.Z := by rw [hsl]; omega_arith
  refine WP.mono (sieve_ok oddPrimes256 (by decide) h.st.scr h.st.r31 h.ph.r10 h.ph.r11 h.n (by omega_arith)
    (by omega_arith) hZw (by omega_arith)) fun t ⟨⟨hb, f⟩, k⟩ => ?_
  obtain ⟨st, ph, hU⟩ := shapeStep h.st h.ph h.u f (fun r hr => .inl (List.mem_singleton.mp hr)) k
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨st, ph, hU, ?_, hb.trans (and_congr h.bad Iff.rfl)⟩
  rw [f.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, hsl]; exact .inr (by decide)) (by omega_arith)]; exact h.n

/-- q from p. -/
theorem MB.halve {p : PP} {x : Nat} {B : Prop} {s : State} (h : MB p x B s) :
    WP isa halveQ s (MB p (x / 2) (B ∧ x / 2 % 2 = 1)) := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hdn := h.st.dims.n
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hZw : slot (wOf p.bits) 0 + 8 * wOf p.bits ≤ p.Z := by rw [hsl]; omega_arith
  refine WP.mono (halveQ_ok h.st h.ph.r10 h.ph.r11 h.n (by omega_arith) (by omega_arith) hZw) fun t ⟨⟨hn, hb, f⟩, k⟩ => ?_
  obtain ⟨st, ph, hU⟩ := shapeStep h.st h.ph h.u f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hsl]; exact .inr rfl
    · exact .inl rfl) k (by decide) (by decide) (by decide) (by decide)
  exact ⟨st, ph, hU, hn, hb.trans (and_congr h.bad Iff.rfl)⟩

/-- `main`: p, its shape, and the tests. -/
theorem main_ok (R : RoundImpl) {p : PP} {s : State} (h : St p s)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (main R.name R.code) s (CEnd p (checkedCandidate p.bits p.g p.r)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  rw [checked_eq hL]
  generalize hc : Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take ((p.bits + 7) / 8))) = c
  have hc' : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) := hc.symm
  have hsh := shape_iff (x := Spec.Rsa.os2ip (p.r.take p.L)) hb1 hb2 h.dims.g
  obtain ⟨ho, hl, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
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
    omega_arith
  unfold main
  refine WP.assoc (WP.seq (WP.mono (mainA_ok h hU hL) fun t₂ ⟨st₂, ph₂, hU₂, hn₂⟩ => ?_))
  rw [← hc'] at hn₂
  refine WP.seq (WP.mono (residue_mb st₂ ph₂ hU₂ hn₂) fun t₃ M₃ => ?_)
  refine WP.seq (WP.mono M₃.badLoad fun t₄ ⟨M₄, t5⟩ => ?_)
  refine WP.ite (word t₃.mem p.B 200 == 0) (by rw [eval_zero, t5]) (fun hz => ?_) (fun hz => ?_)
  rotate_left
  · -- The congruence fails.
    refine reject M₄.st M₄.u (Bool.eq_false_iff.mpr fun ht => ?_)
    have h0 : word t₃.mem p.B 200 = 0#64 := M₃.bad.mpr (hsh.mpr ht).1
    simp [h0] at hz
  refine WP.seq (WP.mono M₄.sieve fun t₅ M₅ => ?_)
  refine WP.seq (WP.mono M₅.halve fun t₆ M₆ => ?_)
  refine WP.seq (WP.mono M₆.sieve fun t₇ M₇ => ?_)
  refine WP.seq (WP.mono M₇.badLoad fun t₈ ⟨M₈, t5'⟩ => ?_)
  have hall : word t₇.mem p.B (8 * hBad) = 0#64 ↔
      goodRes p.g c ∧ (∀ d ∈ oddPrimes256, c % d ≠ 0) ∧ c / 2 % 2 = 1 ∧ ∀ d ∈ oddPrimes256, c / 2 % d ≠ 0 :=
    M₇.bad.trans ⟨fun ⟨⟨⟨a, b⟩, c'⟩, d⟩ => ⟨a, b, c', d⟩, fun ⟨a, b, c', d⟩ => ⟨⟨⟨a, b⟩, c'⟩, d⟩⟩
  refine WP.ite (word t₇.mem p.B 200 == 0) (by rw [eval_zero, t5']) (fun hz' => ?_) (fun hz' => ?_)
  · -- The shape passes: the tests.
    have hshape := hsh.mp (hall.mp (beq_iff_eq.mp hz'))
    rw [hshape]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hq : (c - 1) / 2 = c / 2 := by omega_arith
    obtain ⟨_, _, hqo, _⟩ := hall.mp (beq_iff_eq.mp hz')
    rw [hc'] at hq hqo ⊢
    refine tests_ok R M₈.st rfl ?_ (by rw [hq]; exact hqo) M₈.u hL
    rw [hq, ← hc']; exact M₈.n
  · refine reject M₈.st M₈.u (Bool.eq_false_iff.mpr fun ht => ?_)
    have h0 : word t₇.mem p.B 200 = 0#64 := hall.mpr (hsh.mpr ht)
    simp [h0] at hz'

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
