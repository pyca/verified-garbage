module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.DrawFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCallCT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Round
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.RelCTChain
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.DrawFn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCallCT

/-!
# An FFDH parameter candidate on PPC64LE: a draw in constant time

Two runs draw the same witness from the same tape (`DI`), whatever the
registers saved on entry: `PP.with` gives the public data `q` the saved
registers of one run. The head pins the tape's address and the count it
loads; the pieces up to the range check are then checked by the taint
analysis; the branches are on the witness's range and its round's result,
which `q` decides.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)

/-- `p`'s public data with a run's saved registers and `r2`. -/
def PP.with (p : PP) (sv : Nat → BitVec 64) (toc : BitVec 64) : PP := { p with sv := sv, toc := toc }

/-- A draw's public data. -/
structure DrawD where
  q : PP
  mb : Nat
  N : Nat
  u : Nat
  i : Nat

/-- Before a draw. -/
def DI (d : DrawD) (s : State) : Prop :=
  ∃ sv toc, MSt (d.q.with sv toc) d.mb d.N s ∧ word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧
    d.u + (d.mb + 7) / 8 ≤ d.q.r.length ∧ word s.mem d.q.B 176 = BitVec.ofNat 64 d.i ∧
    word s.mem d.q.B 160 = BitVec.ofNat 64 4 ∧ d.i < 2 ^ 62

theorem pins_DI : Pins DI [.r29, .r31] := by
  rintro d s₁ s₂ ⟨_, _, h₁, -⟩ ⟨_, _, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.ph.r29, h₂.ph.r29]
  · rw [h₁.st.r31, h₂.st.r31]; rfl

/-- After a draw's head. -/
def DA (d : DrawD) (t : State) : Prop :=
  ∃ sv toc s, (MSt (d.q.with sv toc) d.mb d.N s ∧ word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧
    d.u + (d.mb + 7) / 8 ≤ d.q.r.length ∧ word s.mem d.q.B 176 = BitVec.ofNat 64 d.i ∧
    word s.mem d.q.B 160 = BitVec.ofNat 64 4 ∧ d.i < 2 ^ 62) ∧ DHead (d.q.with sv toc) d.mb d.u s t

theorem pins_DA : Pins DA [.r6, .r10, .r11, .r12, .r29, .r31] := by
  rintro d s₁ s₂ ⟨_, _, _, ⟨M₁, -⟩, ⟨a12, a6, a10, -⟩, k₁⟩ ⟨_, _, _, ⟨M₂, -⟩, ⟨b12, b6, b10, -⟩, k₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a6, b6]
  · rw [a10, b10]; rfl
  · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), M₁.ph.r11, M₂.ph.r11]
  · rw [a12, b12]; rfl
  · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), M₁.ph.r29, M₂.ph.r29]
  · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), M₁.st.r31, M₂.st.r31]; rfl

theorem drawHead_ct : RelCT isa (Two DI) (.block ([ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK,
    .add .r3 .r3 .r6, sth .r3 hUsed] ++ base .r10 4)) (Two DA) :=
  two_post (two_taint _ pins_DI (by taint_decide)) fun _ s ⟨sv, toc, M, hu, hroom, hI, hS, hi⟩ =>
    WP.mono (dHead_ok ⟨M.st, M.ph, M.prep, hu, hroom, M.mb1, M.mb2⟩) fun t ht =>
      ⟨sv, toc, s, ⟨M, hu, hroom, hI, hS, hi⟩, ht⟩

/-- Before a draw's branches. -/
def DMd (d : DrawD) (t : State) : Prop := ∃ sv toc, DMid (d.q.with sv toc) d.mb d.N d.u d.i t ∧ d.i < 2 ^ 62

theorem drawMid_ct : RelCT isa (Two DA) (Prog.chain drawMid (.block [])) (Two DMd) :=
  two_post (two_taint _ pins_DA (by taint_decide)) fun _ _ ⟨sv, toc, _, ⟨M, hu, hroom, hI, hS, hi⟩, ht⟩ =>
    WP.mono (drawRest_ok M hu hroom hI hS ht) fun _ h' => ⟨sv, toc, h', hi⟩

theorem beq_zero_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0#64 ↔ P) : (x == 0) = decide P := by
  apply Bool.eq_iff_iff.mpr; rw [beq_iff_eq, decide_eq_true_iff]; exact h

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The round's call, from a witness in range. -/
def rcOf (d : DrawD) : RcD := ⟨d.q.B, d.q.n, wOf d.mb, d.N, wA d.mb d.q.r d.u⟩

/-- After the round. -/
def DR (d : DrawD) (t : State) : Prop :=
  t.gpr .r3 = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u) then 1 else 0) ∧ t.gpr .r31 = d.q.B

theorem pins_DR : Pins DR [.r31] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

theorem round_ct (R : RoundImpl) : RelCT isa (Two fun d s => (DMd d s ∧ decide (wA d.mb d.q.r d.u < 2) = false) ∧
    decide (¬ wA d.mb d.q.r d.u < d.N - 1) = false) (round R.name R.code) fun _ _ => True := by
  have hrc : ∀ d s, ((DMd d s ∧ decide (wA d.mb d.q.r d.u < 2) = false) ∧
      decide (¬ wA d.mb d.q.r d.u < d.N - 1) = false) → RC (rcOf d) s := by
    rintro d s ⟨⟨⟨sv, toc, h, _⟩, h2⟩, hN⟩
    simp only [decide_eq_false_iff_not, Decidable.not_not] at h2 hN
    have hsp := h.m.st.sp
    exact ⟨h.m.prep, h.a4, show wA d.mb d.q.r d.u < d.N by omega, by rw [hsp]; exact h.m.st.stk, by rw [hsp]; exact h.m.st.stkB⟩
  unfold Impl.MillerRabin.PPC64LE.Search.round
  refine RelCT.seq (two_post (two_map rcOf hrc (roundCall_ct R)) (Ψ := DR) fun d s h => ?_) ?_
  · obtain ⟨hp, ha, hac, hsp, hstk⟩ := hrc d s h
    exact WP.mono (roundCall_ok R hp ha hac hsp hstk) fun t ht => ⟨ht.r3, ht.prep.env.h31⟩
  refine two_ite' (fun d => !Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u)) (fun d s h => ?_)
    (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_DR d s₁ s₂ h₁.1 h₂.1) (by taint_decide))
    (two_taint _ (fun d s₁ s₂ h₁ h₂ => pins_DR d s₁ s₂ h₁.1 h₂.1) (by taint_decide))
  rw [eval_zero, h.1]
  cases Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u) <;> rfl

theorem drawBranch_ct (R : RoundImpl) : RelCT isa (Two DMd) (drawBranch R.name R.code) fun _ _ => True := by
  unfold drawBranch
  refine two_ite' (fun d => decide (wA d.mb d.q.r d.u < 2)) (fun d s ⟨sv, toc, h, _⟩ => by
      rw [eval_zero, beq_zero_of_iff h.z24]; rfl)
    (two_taint _ (pins_nil _) (by taint_decide)) ?_
  refine two_ite' (fun d => decide (¬ wA d.mb d.q.r d.u < d.N - 1)) (fun d s ⟨⟨sv, toc, h, _⟩, _⟩ => by
      rw [eval_zero, beq_zero_of_iff h.z20]; rfl)
    (two_taint _ (pins_nil _) (by taint_decide)) (round_ct R)

/-- A draw leaks the same from the same public data. -/
theorem draw_ct (R : RoundImpl) : RelCT isa (Two DI) (draw R.name R.code) fun _ _ => True := by
  rw [draw_eq]
  exact RelCT.seq drawHead_ct (RelCT.chain (RelCT.seq drawMid_ct (drawBranch_ct R)))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
