module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTTests
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Main
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTTests
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Main

/-!
# An FFDH parameter candidate on PPC64LE: `main` in constant time

p's congruence branches on the generator, pinned once loaded; the shape
checks branch on `hBad`, which the candidate decides (`MB`); the tests are
`tests_ct`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- The candidate from the tape. -/
def candOf (q : PP) : Nat := Spec.Ffdh.candidateOf q.bits (Spec.Rsa.os2ip (q.r.take q.L))

/-- Before `main`. -/
def MnI (q : PP) (s : State) : Prop :=
  ∃ sv toc, St (q.with sv toc) s ∧ word s.mem q.B 152 = BitVec.ofNat 64 q.L ∧ q.L ≤ q.r.length

/-- With p in array 0. -/
def MnA (q : PP) (t : State) : Prop :=
  (∃ sv toc, St (q.with sv toc) t ∧ Ph (q.with sv toc) q.bits t ∧ word t.mem q.B 152 = BitVec.ofNat 64 q.L ∧
    wv t.mem q.B (slot (wOf q.bits) 0) (wOf q.bits) = candOf q) ∧ q.L ≤ q.r.length

/-- In p's working space, `hBad` zero iff `B q`. -/
def MnB (x : PP → Nat) (B : PP → Prop) (q : PP) (t : State) : Prop :=
  (∃ sv toc, MB (q.with sv toc) (x q) (B q) t) ∧ q.L ≤ q.r.length

theorem pins_MnB {x : PP → Nat} {B : PP → Prop} {Φ : PP → State → Prop} (h : ∀ q s, Φ q s → MnB x B q s) :
    Pins Φ [.r10, .r11, .r29, .r31] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨⟨_, _, M₁⟩, _⟩ := h q s₁ h₁
  obtain ⟨⟨_, _, M₂⟩, _⟩ := h q s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [M₁.ph.r10, M₂.ph.r10]; rfl
  · rw [M₁.ph.r11, M₂.ph.r11]; rfl
  · rw [M₁.ph.r29, M₂.ph.r29]; rfl
  · rw [M₁.st.r31, M₂.st.r31]; rfl

theorem mainA_ct : RelCT isa (Two MnI) (.seq (phase false) shapeP) (Two MnA) :=
  two_post (two_mono (fun _ _ ⟨sv, toc, h, _⟩ => ⟨sv, toc, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct))
    fun _ _ ⟨sv, toc, h, hU, hL⟩ => WP.mono (mainA_ok h hU hL) fun _ ⟨a, b, c, d⟩ => ⟨⟨sv, toc, a, b, c, d⟩, hL⟩

/-- After the congruence's first block. -/
def RH (q : PP) (t : State) : Prop :=
  (t.gpr .r3 = BitVec.ofNat 64 q.g - BitVec.ofNat 64 2 ∧ (q.g = 2 ∨ q.g = 5)) ∧
    t.gpr .r10 = off q.B (slot (wOf q.bits) 0) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wOf q.bits) ∧ t.gpr .r31 = q.B

theorem pins_RH {Φ : PP → State → Prop} (h : ∀ q s, Φ q s → RH q s) : Pins Φ [.r10, .r11, .r31] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨_, a10, a11, a31⟩ := h q s₁ h₁
  obtain ⟨_, b10, b11, b31⟩ := h q s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a31, b31]

theorem pins_MnA : Pins MnA [.r31] := by
  rintro q s₁ s₂ ⟨⟨_, _, h₁, _⟩, _⟩ ⟨⟨_, _, h₂, _⟩, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.r31, h₂.r31]; rfl

theorem residue_ct : RelCT isa (Two MnA) residue (Two (MnB candOf fun q => goodRes q.g (candOf q))) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, toc, h, hp, hU, hn⟩, hL⟩ =>
    WP.mono (residue_mb h hp hU hn) fun _ M => ⟨⟨sv, toc, M⟩, hL⟩
  unfold residue
  refine RelCT.seq (two_post (two_taint _ pins_MnA (by taint_decide)) (Ψ := RH)
    fun q s ⟨⟨sv, toc, h, hp, _⟩, _⟩ => ?_) (two_ite' (fun q => decide (q.g = 2)) (fun q s h => ?_)
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide))
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide)))
  · refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 q.g - BitVec.ofNat 64 2) ?_ (by decide))
      fun t ⟨t3, k⟩ => ⟨⟨t3, h.dims.g⟩, (k.gpr _ (by decide)).trans hp.r10, (k.gpr _ (by decide)).trans hp.r11,
        (k.gpr _ (by decide)).trans h.r31⟩
    simp only [ldh, hGen]
    prun [h.r31, h.ld (d := 128) (by decide), h.args.gen', BitVec.add_zero]
    rfl
  · obtain ⟨⟨h3, hg⟩, _⟩ := h
    rw [eval_zero, h3]
    rcases hg with hg | hg <;> rw [hg] <;> decide

theorem badLoad_ct {x : PP → Nat} {B : PP → Prop} [∀ q, Decidable (B q)] :
    RelCT isa (Two (MnB x B)) (.block [ldh .r5 hBad])
      (Two fun q t => MnB x B q t ∧ isa.eval (.zero .d .r5) t = some (decide (B q))) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ =>
    WP.mono M.badLoad fun _ ⟨M', t5⟩ => ⟨⟨⟨sv, toc, M'⟩, hL⟩,
      (by rw [eval_zero, t5]; exact congrArg some (beq_zero_of_iff M.bad))⟩

theorem finMnB_ct {x : PP → Nat} {B : PP → Prop} {Φ : PP → State → Prop} (h : ∀ q s, Φ q s → MnB x B q s) :
    RelCT isa (Two Φ) (.block (finish 2)) fun _ _ => True :=
  two_mono (fun q s hs => let ⟨⟨_, _, M⟩, _⟩ := h q s hs; M.st.fs) (finish_ct (.inr (.inr rfl)))

theorem sieve_ct {x : PP → Nat} {B : PP → Prop} {Φ : PP → State → Prop} (h : ∀ q s, Φ q s → MnB x B q s) :
    RelCT isa (Two Φ) VG.Impl.Ffdh.PPC64LE.ParameterCandidate.sieve
      (Two (MnB x fun q => B q ∧ ∀ d ∈ oddPrimes256, x q % d ≠ 0)) :=
  two_post (two_taint _ (pins_MnB h) (by taint_decide)) fun q s hs =>
    let ⟨⟨sv, toc, M⟩, hL⟩ := h q s hs; WP.mono M.sieve fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩

theorem halve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) halveQ (Two (MnB (fun q => x q / 2) fun q => B q ∧ x q / 2 % 2 = 1)) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ =>
    WP.mono M.halve fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩

/-- The shape checks' conjunction, after both sieves. -/
def allOk (q : PP) : Prop :=
  ((goodRes q.g (candOf q) ∧ ∀ d ∈ oddPrimes256, candOf q % d ≠ 0) ∧ candOf q / 2 % 2 = 1) ∧
    ∀ d ∈ oddPrimes256, candOf q / 2 % d ≠ 0

instance (q : PP) : Decidable (allOk q) := by unfold allOk; infer_instance

theorem ts_of {q : PP} {s : State} (h : MnB (fun q => candOf q / 2) allOk q s) (ha : allOk q) :
    TS ⟨q, candOf q, q.L⟩ s := by
  obtain ⟨⟨sv, toc, M⟩, hL⟩ := h
  have hb1 : 512 ≤ q.bits := M.st.dims.b1
  obtain ⟨ho, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := q.bits) (by omega)
    (Spec.Rsa.os2ip (q.r.take q.L))
  have hq : (candOf q - 1) / 2 = candOf q / 2 := by unfold candOf; omega
  refine ⟨⟨sv, toc, M.st, rfl, by rw [hq]; exact M.n, by rw [hq]; exact ha.1.2, M.u, hL⟩, hL⟩

/-- `main` leaks the same from the same arguments and tape. -/
theorem main_ct (R : RoundImpl) : RelCT isa (Two MnI) (main R.name R.code) fun _ _ => True := by
  unfold main
  refine RelCT.assoc (RelCT.seq mainA_ct (RelCT.seq residue_ct (RelCT.seq badLoad_ct
    (two_ite' (fun q => decide (goodRes q.g (candOf q))) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1)))))
  refine RelCT.seq (sieve_ct fun _ _ h => h.1.1) (RelCT.seq halve_ct (RelCT.seq (sieve_ct fun _ _ h => h)
    (RelCT.seq (badLoad_ct (B := allOk)) (two_ite' (fun q => decide (allOk q)) (fun _ _ h => h.2) ?_
      (finMnB_ct fun _ _ h => h.1.1)))))
  exact two_map (fun q => (⟨q, candOf q, q.L⟩ : TQD)) (fun _ _ ⟨⟨h, _⟩, ha⟩ => ts_of h (of_decide_eq_true ha))
    (tests_ct R)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
