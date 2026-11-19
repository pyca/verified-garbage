module

import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Loop
import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Loop
meta import VerifiedGarbage.Proof.MlDsa.Sign.Leak
meta import VerifiedGarbage.Proof.MlDsa.Sign.Iter
meta import VerifiedGarbage.Proof.MlDsa.Sign.Setup
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! ### `MlDsa.RISCV64.Sign.LoopCT`, which only this module used -/

section

/-!
# ML-DSA signing on RISC-V: the loop leaks what `signLeakT` says

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/PhaseLCT.lean`): two runs whose
remaining iterations leak the same (`LeakEq`) agree on the iteration's `c̃`
(`leq_ct`), on whether it passes (`leq_pass`) and on its hint if it does
(`leq_hints`), and, if it is rejected, on what the rest leaks (`leq_succ`);
so they agree on the branches of each iteration, and leak the same
(`iter_tr`, `signLoop_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## Runs related through their entry states -/

/-- Two runs from entry states that satisfy the precondition, agree on the
public data and are related by `E`, each related to its entry state by `I`. -/
def RS (p : Params) (STK : Nat) (E I : State → State → Prop) (x y : State) : Prop :=
  ∃ σ₁ σ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧ E σ₁ σ₂ ∧ I σ₁ x ∧ I σ₂ y

section
variable {p : Params} {STK : Nat}

theorem RS.rel2 {E I : State → State → Prop} {x y : State} (h : RS p STK E I x y) :
    Rel2 (SPre p STK) (sPub p) I x y := by
  obtain ⟨σ₁, σ₂, p₁, p₂, pub, _, i₁, i₂⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩

/-- A part that takes each run from `I` to `J` (and `s` to `s'` with `F s s'`), and leaks the same from runs
related by `RS E I` and `G`, with `Q₀` of the final states. -/
theorem liftQ {E I J G Q₀ Q F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, SPre p STK σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (fun x y => RS p STK E I x y ∧ G x y) c Q₀)
    (hQ : ∀ σ₁ σ₂ x y x' y', SPre p STK σ₁ → SPre p STK σ₂ → sPub p σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → G x y → J σ₁ x' → J σ₂ y' → F x x' → F y y' → Q₀ x' y' → Q x' y') :
    RelCT isa (fun x y => RS p STK E I x y ∧ G x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩ := hr
  obtain ⟨_, u₁, f₁, j₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, j₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ _ _ _ _ p₁ p₂ hpub he i₁ i₂ hg j₁ j₂ g₁ g₂ hq⟩

/-- A piece keeps runs related by `RS E`. -/
theorem pieceRS {E I J : State → State → Prop} {c : Prog isa} (h : SPiece p STK I J c) :
    RelCT isa (RS p STK E I) c (RS p STK E J) := by
  refine RelCT.mono (liftQ (G := fun _ _ => True) (F := fun _ _ => True) (J := J) (Q := RS p STK E J)
    (fun σ s hp hs => WP.mono (h.ok σ s hp hs) fun _ h => ⟨h, trivial⟩)
    (RelCT.mono h.tr (fun _ _ h => h.1.rel2) fun _ _ h => h)
    fun σ₁ σ₂ _ _ _ _ p₁ p₂ pub he _ _ _ j₁ j₂ _ _ _ => ⟨σ₁, σ₂, p₁, p₂, pub, he, j₁, j₂⟩)
    (fun _ _ h => ⟨h, trivial⟩) fun _ _ h => h

theorem RS.mono {E I J : State → State → Prop} {x y : State} (h : RS p STK E I x y) (hI : ∀ σ s, I σ s → J σ s) :
    RS p STK E J x y := by
  obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, i₁, i₂⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, pub, he, hI _ _ i₁, hI _ _ i₂⟩

theorem relOr {P₁ P₂ Q : State → State → Prop} {c : Prog isa} (h₁ : RelCT isa P₁ c Q) (h₂ : RelCT isa P₂ c Q) :
    RelCT isa (fun x y => P₁ x y ∨ P₂ x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  rcases hr with h | h
  exacts [h₁ _ _ _ _ _ _ h e₁ e₂, h₂ _ _ _ _ _ _ h e₁ e₂]

end

/-! ## What the iterations leak -/

section
variable (p : Params)

/-- What the `n` iterations from counter `κ` leak, for the function entered in `σ`. -/
abbrev leakL (σ : State) (n κ : Nat) : List Nat :=
  signLeakLoop p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) n κ

/-- Two runs agree on what the iterations from `t` leak. -/
abbrev LeakEq (t : Nat) (σ₁ σ₂ : State) : Prop := leakL p σ₁ (1000 - t) (p.ℓ * t) = leakL p σ₂ (1000 - t) (p.ℓ * t)

end

theorem map_toNat_inj : ∀ {l₁ l₂ : List Bool}, l₁.map Bool.toNat = l₂.map Bool.toNat → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [map_toNat_inj h.2]
    cases a <;> cases b <;> simp_all
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem hints_inj : ∀ {a b : List (Vector Bool n)}, a.length = b.length →
    (a.flatMap fun hi => hi.toList.map Bool.toNat) = (b.flatMap fun hi => hi.toList.map Bool.toNat) → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    rw [Vector.toList_inj.mp (map_toNat_inj h1), hints_inj (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

section
variable {p : Params} {σ₁ σ₂ : State} {t : Nat}

theorem leq_step (h : LeakEq p t σ₁ σ₂) (ht : t < 814) :
    signLeakLoop p maxBounds (amat p (Am p σ₁)) ((List.range p.ℓ).map (S1v p σ₁)) ((List.range p.k).map (S2v p σ₁))
      ((List.range p.k).map (T0v p σ₁)) (muOf σ₁) (rppOf p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoop p maxBounds (amat p (Am p σ₂)) ((List.range p.ℓ).map (S1v p σ₂)) ((List.range p.k).map (S2v p σ₂))
      ((List.range p.k).map (T0v p σ₂)) (muOf σ₂) (rppOf p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega_using [ht]]; exact h

theorem leq_ct (h : LeakEq p t σ₁ σ₂) (ht : t < 814) : CTv p σ₁ (p.ℓ * t) = CTv p σ₂ (p.ℓ * t) := by
  have := (leakF_step (leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakF_step (leq_step h ht)).2.1 hr).2
  unfold LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega_using [], Nat.mul_succ]
  exact this

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat}
    (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    outTag (iterF p σ maxBounds κ) = if PassV p σ κ then
      1 :: ((List.range p.k).map (Hv p σ κ)).flatMap (fun hi => hi.toList.map Bool.toNat) else [0] := by
  rw [iterF_eq hp, cV_eq hs, Option.map_some]
  by_cases hv : PassV p σ κ
  · rw [ifp hv, ifp hv]; rfl
  · rw [ifn hv, ifn hv]; rfl

theorem leq_pass (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) :
    PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t) := by
  have e := (leakF_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂] at e
  by_cases h1 : PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [ifp h1, ifn h2] at e; cases e
  · rw [ifn h1, ifp h2] at e; cases e
  · exact iff_of_false h1 h2

/-- `signRejectTag`'s value: which check failed, and for those of `z` and
`r₀` the first polynomial that failed it. -/
def tagFn (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] (x y : Nat) : Nat :=
  if ¬ a then 5 * x else if ¬ b then 2 + 5 * y else if ¬ c then 3 else 4

theorem tagFn_eq {a b c a' b' c' : Prop} [Decidable a] [Decidable b] [Decidable c] [Decidable a'] [Decidable b']
    [Decidable c'] {x y x' y' : Nat} (h : tagFn a b c x y = tagFn a' b' c' x' y') :
    (a ↔ a') ∧ (¬ a → x = x') ∧ (a ∧ b ↔ a' ∧ b') ∧ (a → ¬ b → y = y') := by
  unfold tagFn at h
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases ha' : a' <;> by_cases hb' : b' <;>
    by_cases hc' : c' <;> simp only [ha, hb, hc, ha', hb', hc', not_true_eq_false, not_false_eq_true,
      ite_true, ite_false] at h <;> first | omega | (simp_all <;> omega_using [h])

/-- The first polynomial of `z` that fails its check, or `ℓ`. -/
abbrev zFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.ℓ).findIdx fun r => decide (normRq [Zv p σ κ r] ≥ p.γ₁ - p.β)

/-- The first polynomial of `r₀` that fails its check, or `k`. -/
abbrev rFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.k).findIdx fun i => decide (normRq [R0v p σ κ i] ≥ p.γ₂ - p.β)

theorem tag_eq (hp : ParamsOk p) {σ : State} {κ : Nat}
    (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    signRejectTag p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
      ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) κ =
      tagFn (ZOk p σ κ) (R0Ok p σ κ) (∀ j < p.k, normRq [CT0v p σ κ j] < p.γ₂) (zFirst p σ κ) (rFirst p σ κ) := by
  rw [signRejectTag_eqF hp, show ctF p (Am p σ) (muOf σ) (rppOf p σ) κ = CTv p σ κ from rfl, cV_eq hs]
  rfl

/-- The first `r ≤ n` polynomials pass a check exactly when the first that
fails it comes at `r` or later. -/
theorem prefix_ok {n B : Nat} (f : Nat → Poly) {r : Nat} (hr : r ≤ n) :
    (∀ j < r, normRq [f j] < B) ↔ r ≤ (List.range n).findIdx fun j => decide (normRq [f j] ≥ B) := by
  rw [← prefix_findIdx n _ hr]
  simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]

/-- Two runs that agree on what the iterations from `t` leak agree on the
checks of iteration `t` that pass, polynomial by polynomial. -/
theorem leq_agree (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) : ChecksAgree p t σ₁ σ₂ := by
  have hpass := leq_pass hp h ht hs₁ hs₂
  by_cases h1 : PassV p σ₁ (p.ℓ * t)
  · have h2 := hpass.mp h1
    exact ⟨fun r hr => iff_of_true (fun j hj => h1.1 j (by omega_using [hr, hj])) (fun j hj => h2.1 j (by omega_using [hr, hj])),
      fun i hi => iff_of_true ⟨h1.1, fun j hj => h1.2.1 j (by omega_using [hi, hj])⟩ ⟨h2.1, fun j hj => h2.2.1 j (by omega_using [hi, hj])⟩, hpass⟩
  · have h2 : ¬ PassV p σ₂ (p.ℓ * t) := fun h2 => h1 (hpass.mpr h2)
    have e := leakF_tag (leq_step h ht) (iter_rej hp hs₁ h1) (iter_rej hp hs₂ h2)
    rw [tag_eq hp hs₁, tag_eq hp hs₂] at e
    obtain ⟨ea, ex, eab, ey⟩ := tagFn_eq e
    refine ⟨fun r hr => ?_, fun i hi => ?_, hpass⟩
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · exact iff_of_true (fun j hj => hz j (by omega_using [hr, hj])) (fun j hj => ea.mp hz j (by omega_using [hr, hj]))
      · rw [prefix_ok _ hr, prefix_ok _ hr]; exact iff_of_eq (congrArg (r ≤ ·) (ex hz))
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · have hz' := ea.mp hz
        by_cases hr0 : R0Ok p σ₁ (p.ℓ * t)
        · have hr0' := (eab.mp ⟨hz, hr0⟩).2
          exact iff_of_true ⟨hz, fun j hj => hr0 j (by omega_using [hi, hj])⟩ ⟨hz', fun j hj => hr0' j (by omega_using [hi, hj])⟩
        · rw [and_iff_right hz, and_iff_right hz', prefix_ok _ hi, prefix_ok _ hi]
          exact iff_of_eq (congrArg (i ≤ ·) (ey hz hr0))
      · exact iff_of_false (fun h => hz h.1) (fun h => hz (ea.mpr h.1))

theorem leq_hints (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome)
    (h1 : PassV p σ₁ (p.ℓ * t)) (h2 : PassV p σ₂ (p.ℓ * t)) :
    (List.range p.k).map (Hv p σ₁ (p.ℓ * t)) = (List.range p.k).map (Hv p σ₂ (p.ℓ * t)) := by
  have e := (leakF_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂, ifp h1, ifp h2] at e
  exact hints_inj (by simp) (List.cons.inj e).2

end

/-! ## An iteration -/

/-- The loop ended in both runs: they agree on whether it succeeded, and if it did, on the hint. -/
def OX (p : Params) (STK : Nat) (x y : State) : Prop :=
  ∃ σ₁ σ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧ XS p STK σ₁ x ∧ XS p STK σ₂ y ∧
    x.gpr .s4 = y.gpr .s4 ∧ (x.gpr .s4 = 1 → ∃ f : Nat → Vector Bool n,
      (∀ i < p.k, HintIs x.mem (SL p STK σ₁ (5 + i)) 1 [f i]) ∧ ∀ i < p.k, HintIs y.mem (SL p STK σ₁ (5 + i)) 1 [f i])

/-- After iteration `t` of two runs: both continue, leaking the same from then on, or both end. -/
def IX (p : Params) (STK : Nat) (t : Nat) (x y : State) : Prop :=
  x.gpr .s5 = y.gpr .s5 ∧ (x.gpr .s5 ≠ 0 → RS p STK (LeakEq p (t + 1)) (IL p STK · (t + 1)) x y) ∧
    (x.gpr .s5 = 0 → OX p STK x y)

theorem LP.il {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : LP p STK σ t s) (hz : s.gpr .s5 ≠ 0) :
    IL p STK σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h hz

theorem LP.xs {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : LP p STK σ t s) (hz : s.gpr .s5 = 0) :
    XS p STK σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd hz h
  · exact h

/-- The taint check of `κ ← κ + ℓ` does not depend on `ℓ`. -/
theorem kapAdd_taint (l : Nat) : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) (.block [.addi .s7 .s7 l])
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s11]) (.block [.addi .s7 .s7 4]))).isSome = true := rfl

theorem nil_tr {Q R : State→State→Prop} (h:∀x y,R x y→Q x y) : RelCT isa R (.block []) Q := by
  intro _ _ _ _ _ _ hr e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl,rfl⟩:=e₁
  obtain ⟨rfl,rfl⟩:=e₂
  exact ⟨rfl,h _ _ hr⟩

section
variable {p : Params} {STK : Nat}

theorem ifOkElse_RS {E I Q : State→State→Prop} {a b : Prog isa}
    (heq:∀ x y,RS p STK E I x y→x.gpr .s4=y.gpr .s4)
    (ha:RelCT isa (RS p STK E fun σ s=>I σ s ∧ s.gpr .s4≠0) a Q)
    (hb:RelCT isa (RS p STK E fun σ s=>I σ s ∧ s.gpr .s4=0) b Q) :
    RelCT isa (RS p STK E I) (ifOkElse a b) Q := by
  refine RelCT.ite (fun x y h=>by rw [Steps.eval_nonzero,Steps.eval_nonzero,heq x y h]) ?_ ?_
  · refine RelCT.mono ha (fun x y ⟨h,hb⟩=>?_) (fun _ _ h=>h)
    have hx:x.gpr .s4≠0:=by rw [Steps.eval_nonzero] at hb; simpa using hb
    obtain ⟨σ,τ,p₁,p₂,pub,he,h₁,h₂⟩:=h
    exact ⟨σ,τ,p₁,p₂,pub,he,⟨h₁,hx⟩,⟨h₂,(heq x y ⟨σ,τ,p₁,p₂,pub,he,h₁,h₂⟩) ▸ hx⟩⟩
  · refine RelCT.mono hb (fun x y ⟨h,hb⟩=>?_) (fun _ _ h=>h)
    have hx:x.gpr .s4=0:=by rw [Steps.eval_nonzero] at hb; simpa using hb
    obtain ⟨σ,τ,p₁,p₂,pub,he,h₁,h₂⟩:=h
    exact ⟨σ,τ,p₁,p₂,pub,he,⟨h₁,hx⟩,⟨h₂,(heq x y ⟨σ,τ,p₁,p₂,pub,he,h₁,h₂⟩) ▸ hx⟩⟩

theorem seqOk_RS {E : State→State→Prop} {I : Nat→State→State→Prop} {f : Nat→Prog isa} :
    ∀ (n a : Nat),
      (∀ k,a<k→k≤a+n→∀ x y,RS p STK E (I k) x y→x.gpr .s4=y.gpr .s4) →
      (∀ k,a≤k→k<a+n→RelCT isa (RS p STK E (I k)) (f k) (RS p STK E (I (k+1)))) →
      RelCT isa (RS p STK E (I a)) (seqOk f a n)
        (RS p STK E fun σ s=>∃k,a≤k ∧ k≤a+n ∧ I k σ s ∧ (k=a+n ∨ s.gpr .s4=0))
  | 0,a,_,_=>RelCT.mono (nil_tr (fun _ _ h=>h)) (fun _ _ h=>h) fun _ _ h=>
      h.mono (fun _ _ hi=>⟨a,Nat.le_refl _,by omega_using [],hi,.inl (by omega_using [])⟩)
  | n+1,a,hq,h=>by
    rw [seqOk]
    refine RelCT.seq (h a (Nat.le_refl _) (by omega_using [])) ?_
    refine ifOkElse_RS (hq (a+1) (by omega_using []) (by omega_using [])) ?_ ?_
    · refine RelCT.mono (seqOk_RS n (a+1) (fun k hk hk'=>hq k (by omega_using [hk]) (by omega_using [hk']))
        (fun k hk hk'=>h k (by omega_using [hk]) (by omega_using [hk']))) (fun _ _ hi=>hi.mono fun _ _ hi=>hi.1) ?_
      intro _ _ hi
      exact hi.mono fun _ _ ⟨k,hk,hk',hi,hd⟩=>⟨k,by omega_using [hk],by omega_using [hk'],hi,hd.imp (fun _=>by omega_arith) id⟩
    · exact nil_tr fun _ _ hi=>hi.mono fun _ _ ⟨hi,hz⟩=>⟨a+1,by omega_using [],by omega_using [],hi,.inr hz⟩

end

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
  (hp : ParamsOk p)
include hP hF hS hp

omit hP hF hS in
theorem ep_ef_tr {t : Nat} :
    RelCT isa (fun x y => RS p STK (LeakEq p t) (fun σ s => EP p STK σ t s ∨ EF p STK σ t s) x y ∧ True)
      (.block [.addi .s5 .s5 (-1)]) (IX p STK t) := by
  refine liftQ (J := fun σ s => LP p STK σ t s) (F := fun s s' => W1 .s5 (s.gpr .s5 - BitVec.ofNat 64 1) s s')
    (fun σ s _ h => WP.conj (dec_end hp (h.elim .inl (.inr ∘ .inl))) (subi_ok s))
    (RelCT.mono (srel2 (I := fun σ s => EP p STK σ t s ∨ EF p STK σ t s) (fun σ s h => h.elim (·.k.sc) (·.k.sc))
      (by taint_decide)) (fun _ _ h => h.1.rel2) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ w₁ w₂ _
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.gpr .s5 = 0 := by rw [w₁.1, e₁.s5]; decide
    have zy : y'.gpr .s5 = 0 := by rw [w₂.1, e₂.s5]; decide
    have r₁ : x'.gpr .s4 = 1 := by rw [w₁.2.1 .s4 (by decide)]; exact e₁.s4
    have r₂ : y'.gpr .s4 = 1 := by rw [w₂.2.1 .s4 (by decide)]; exact e₂.s4
    refine ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨σ₁, σ₂, p₁, p₂, hpub, j₁.xs zx, j₂.xs zy, by rw [r₁, r₂],
      fun _ => ⟨Hv p σ₁ (p.ℓ * t), fun i hi => by rw [w₁.2.2.1]; exact e₁.h i hi, fun i hi => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) i (List.mem_range.mpr hi),
      w₂.2.2.1, SL_pub hpub]
    exact e₂.h i hi
  · exact absurd ((leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.gpr .s5 = y'.gpr .s5 := by rw [w₁.1, w₂.1, f₁.s5, f₂.s5]
    have r₁ : x'.gpr .s4 = 0 := by rw [w₁.2.1 .s4 (by decide)]; exact f₁.s4
    have r₂ : y'.gpr .s4 = 0 := by rw [w₂.2.1 .s4 (by decide)]; exact f₂.s4
    refine ⟨zxy, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, leq_succ he f₁.t_lt ⟨_, iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, j₁.xs h, j₂.xs (zxy ▸ h), by rw [r₁, r₂],
      fun h1 => absurd (h1.symm.trans r₁) (by decide)⟩⟩

omit hP hF hS in
theorem eb_tr {t : Nat} :
    RelCT isa (fun x y => RS p STK (LeakEq p t) (fun σ s => EB p STK σ t s) x y ∧ True)
      (.block [.addi .s5 .s5 (-1)]) (IX p STK t) := by
  refine liftQ (J := fun σ s => LP p STK σ t s) (F := fun s s' => W1 .s5 (s.gpr .s5 - BitVec.ofNat 64 1) s s')
    (fun σ s _ h => WP.conj (dec_end hp (.inr (.inr h))) (subi_ok s))
    (RelCT.mono (srel2 (I := fun σ s => EB p STK σ t s) (fun σ s h => h.k.sc) (by taint_decide))
      (fun _ _ h => h.1.rel2) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ w₁ w₂ _
  have zx : x'.gpr .s5 = 0 := by rw [w₁.1, e₁.s5]; decide
  have zy : y'.gpr .s5 = 0 := by rw [w₂.1, e₂.s5]; decide
  have r₁ : x'.gpr .s4 = 0 := by rw [w₁.2.1 .s4 (by decide)]; exact e₁.s4
  have r₂ : y'.gpr .s4 = 0 := by rw [w₂.2.1 .s4 (by decide)]; exact e₂.s4
  exact ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨σ₁, σ₂, p₁, p₂, hpub, j₁.xs zx, j₂.xs zy, by rw [r₁, r₂],
    fun h1 => absurd (h1.symm.trans r₁) (by decide)⟩⟩


omit hP hF hS hp in
theorem kthen_piece {t : Nat} :
    SPiece p STK (fun σ s => KO p STK σ t s ∧ s.gpr .s4 ≠ 0) (EP p STK · t) (.block [.li .s5 1]) :=
  ⟨fun σ s _ h => kthen_ok h.1 h.2, srel2 (fun σ s h => h.1.b.l.k.sc) (by taint_decide)⟩

omit hP hS hp in
theorem kelse_piece {t : Nat} :
    SPiece p STK (fun σ s => KO p STK σ t s ∧ s.gpr .s4 = 0) (EF p STK · t) (.block [.addi .s7 .s7 p.ℓ]) :=
  ⟨fun σ s _ h => kelse_ok (by have := hF.l; omega_using [this]) h.1 h.2, srel2 (fun σ s h => h.1.b.l.k.sc) (kapAdd_taint p.ℓ)⟩

omit hP hF hS hp in
theorem eb_piece {t : Nat} :
    SPiece p STK (fun σ s => IB p STK σ t s ∧ (s.gpr .a0).setWidth 32 = 0) (EB p STK · t)
      (.block [.li .s4 0, .li .s5 1]) :=
  ⟨fun σ s _ h => eb_ok h.1 h.2, srel2 (fun σ s h => h.1.c.1.l.k.sc) (by taint_decide)⟩

omit hP hF hS hp in
theorem loopInit_piece : SPiece p STK (IK p STK) (IL p STK · 0) (.block [.li .s7 0, .li .s5 814]) :=
  ⟨fun σ s _ h => loopInit_ok h, srel2 (fun σ s h => h.sc) (by taint_decide)⟩

omit hp in
theorem ballRS_tr {t : Nat} (ht : t < 814) :
    RelCT isa (RS p STK (LeakEq p t) (ICd p STK t)) (ballAt P (cLen p) p.τ cP)
      (fun x y => RS p STK (LeakEq p t) (IB p STK · t) x y ∧ (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32) := by
  refine RelCT.mono (liftQ (G := fun _ _ => True) (J := fun σ s => IB p STK σ t s) (F := fun _ _ => True)
    (Q₀ := fun x y => (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32)
    (fun σ s _ h => WP.mono (ball_ok hP hF hS h) fun _ h => ⟨h, trivial⟩) ?_
    fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ _ j₁ j₂ _ _ hq => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, hq⟩)
    (fun x y h => ⟨h, trivial⟩) fun _ _ h => h
  unfold ballAt
  refine RelCT.mono (RelCT.exists_ fun σ => ball_trRet hP hS (ball_m hF (σ := σ)) (name := "vg_mldsa_sample_in_ball")
    (Q := fun x y => Site (slay2 p STK σ) sWb2 STK x ∧ Site (slay2 p STK σ) sWb2 STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa (slay2 p STK σ) (sc oCT)) (cLen p) = bytesAt y.mem (lpa (slay2 p STK σ) (sc oCT)) (cLen p))
    fun _ _ h => h) ?_ fun _ _ h => h
  rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, he, i₁, i₂⟩, -⟩
  have T := sc2_twoL pub i₁.1.l.k.sc i₂.1.l.k.sc
  refine ⟨σ₁, T.1, T.2.1, T.2.2, ?_⟩
  show bytesAt x.mem ((slay2 p STK σ₁).A 0 oCT) (cLen p) = bytesAt y.mem ((slay2 p STK σ₁).A 0 oCT) (cLen p)
  rw [i₁.2, slay2_pub pub, i₂.2]
  exact leq_ct he ht

omit hP hS in
/-- The branch on the result of the checks. -/
theorem kbranch_tr {t : Nat} (ht : t < 814) :
    RelCT isa (RS p STK (LeakEq p t) (KO p STK · t)) (ifOkElse (.block [.li .s5 1]) (.block [.addi .s7 .s7 p.ℓ]))
      (fun x y => (RS p STK (LeakEq p t) (fun σ s => EP p STK σ t s ∨ EF p STK σ t s) x y ∧ True) ∨
        (RS p STK (LeakEq p t) (EB p STK · t) x y ∧ True)) := by
  have e24 : ∀ x y, RS p STK (LeakEq p t) (KO p STK · t) x y → x.gpr .s4 = y.gpr .s4 :=
    fun x y ⟨σ₁, σ₂, _, _, _, he, h₁, h₂⟩ => by
      rw [h₁.s4, h₂.s4]; exact bit_congr (leq_pass hp he ht h₁.b.some h₂.b.some)
  refine RelCT.ite (fun x y h => by rw [Steps.eval_nonzero, Steps.eval_nonzero, e24 x y h]) ?_ ?_
  · refine RelCT.mono (pieceRS (E := LeakEq p t) (kthen_piece (p := p) (STK := STK) (t := t)))
      (fun x y ⟨h, hb⟩ => ?_) fun x y h => .inl ⟨RS.mono h fun _ _ h => .inl h, trivial⟩
    have hx : x.gpr .s4 ≠ 0 := by rw [Steps.eval_nonzero] at hb; simpa using hb
    obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, h₁, h₂⟩ := h
    exact ⟨σ₁, σ₂, p₁, p₂, pub, he, ⟨h₁, hx⟩, ⟨h₂, (e24 x y ⟨σ₁, σ₂, p₁, p₂, pub, he, h₁, h₂⟩) ▸ hx⟩⟩
  · refine RelCT.mono (pieceRS (E := LeakEq p t) (kelse_piece hF (STK := STK) (t := t)))
      (fun x y ⟨h, hb⟩ => ?_) fun x y h => .inl ⟨RS.mono h fun _ _ h => .inr h, trivial⟩
    have hx : x.gpr .s4 = 0 := by rw [Steps.eval_nonzero] at hb; simpa using hb
    obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, h₁, h₂⟩ := h
    exact ⟨σ₁, σ₂, p₁, p₂, pub, he, ⟨h₁, hx⟩, ⟨h₂, (e24 x y ⟨σ₁, σ₂, p₁, p₂, pub, he, h₁, h₂⟩) ▸ hx⟩⟩


theorem checksR0_tr {t:Nat} (ht:t<814) :
    RelCT isa (RS p STK (LeakEq p t) fun σ s=>IQ p STK σ t 0 0 s) (checksR0 P p)
      (RS p STK (LeakEq p t) (KO p STK · t)) := by
  unfold checksR0
  refine RelCT.seq (seqOk_RS (I:=fun i σ s=>IQ p STK σ t i i s) p.k 0
    (fun i _ hi x y ⟨σ,τ,_,_,_,he,h₁,h₂⟩=>by
      rw [h₁.s4,h₂.s4];exact bit_congr ((leq_agree hp he ht h₁.b.some h₂.b.some).2.1 i (by omega_using [hi])))
    (fun i _ hi=>pieceRS (r0R_piece hP hF hS (by omega_using [hi])))) ?_
  refine ifOkElse_RS (fun x y ⟨σ,τ,_,_,_,he,⟨i,_,hi,h₁,hd₁⟩,⟨j,_,hj,h₂,hd₂⟩⟩=>by
    rw [Nat.zero_add] at hi hd₁ hj hd₂
    rw [IQ.done hi h₁ hd₁,IQ.done hj h₂ hd₂]
    exact bit_congr ((leq_agree hp he ht h₁.b.some h₂.b.some).2.1 p.k (Nat.le_refl _))) ?_ ?_
  · refine RelCT.mono (RelCT.seq (pieceRS (hs_piece hP hF hS)) (pieceRS (onesOk_piece hF)))
      (fun _ _ h=>h.mono fun σ s ⟨⟨i,_,hi,h,hd⟩,hn⟩=>?_) (fun _ _ h=>h)
    rw [Nat.zero_add] at hi hd
    have he:i=p.k:=hd.resolve_right hn
    subst he
    exact h.ih
  · refine nil_tr fun _ _ h=>h.mono fun σ s ⟨⟨i,_,hi,h,hd⟩,hz⟩=>?_
    rw [Nat.zero_add] at hi hd
    apply rejected_ko h.b (fun hp=>?_) hz
    exact (bit_ne.mpr ⟨hp.1,hp.2.1⟩) ((IQ.done hi h hd).symm.trans hz)

theorem zchecks_tr {t:Nat} (ht:t<814) :
    RelCT isa (RS p STK (LeakEq p t) fun σ s=>IZ p STK σ t 0 0 s)
      (.seq (seqOk (zR P p) 0 p.ℓ) (ifOk (checksR0 P p))) (RS p STK (LeakEq p t) (KO p STK · t)) := by
  refine RelCT.seq (seqOk_RS (I:=fun i σ s=>IZ p STK σ t i i s) p.ℓ 0
    (fun i _ hi x y ⟨σ,τ,_,_,_,he,h₁,h₂⟩=>by
      rw [h₁.s4,h₂.s4];exact bit_congr ((leq_agree hp he ht h₁.b.some h₂.b.some).1 i (by omega_using [hi])))
    (fun i _ hi=>pieceRS (zR_piece hP hF hS (by omega_using [hi])))) ?_
  refine ifOkElse_RS (fun x y ⟨σ,τ,_,_,_,he,⟨i,_,hi,h₁,hd₁⟩,⟨j,_,hj,h₂,hd₂⟩⟩=>by
    rw [Nat.zero_add] at hi hd₁ hj hd₂
    rw [IZ.done hi h₁ hd₁,IZ.done hj h₂ hd₂]
    exact bit_congr ((leq_agree hp he ht h₁.b.some h₂.b.some).1 p.ℓ (Nat.le_refl _))) ?_ ?_
  · refine RelCT.mono (checksR0_tr hP hF hS hp ht)
      (fun _ _ h=>h.mono fun σ s ⟨⟨i,_,hi,h,hd⟩,hn⟩=>?_) (fun _ _ h=>h)
    rw [Nat.zero_add] at hi hd
    have he:i=p.ℓ:=hd.resolve_right hn
    subst he
    exact h.iq
  · refine nil_tr fun _ _ h=>h.mono fun σ s ⟨⟨i,_,hi,h,hd⟩,hz⟩=>?_
    rw [Nat.zero_add] at hi hd
    apply rejected_ko h.b (fun hp=>?_) hz
    exact (bit_ne.mpr hp.1) ((IZ.done hi h hd).symm.trans hz)

theorem iter_tr {t : Nat} (ht : t < 814) :
    RelCT isa (RS p STK (LeakEq p t) (IL p STK · t)) (iter P p) (IX p STK t) := by
  unfold iter
  refine RelCT.seq (pieceRS (commit_piece hP hF hS)) ?_
  refine RelCT.seq (ballRS_tr hP hF hS ht) ?_
  -- the result zero-extended: equal in both runs, and as its low word says
  have zrel : RelCT isa (fun x y => RS p STK (LeakEq p t) (IB p STK · t) x y ∧
      (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32)
      (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32])
      (fun x y => RS p STK (LeakEq p t) (IB p STK · t) x y ∧ x.gpr .a0 = y.gpr .a0 ∧
        x.gpr .a0 = KeyGen.zx (x.gpr .a0)) :=
    liftQ (J := fun σ s => IB p STK σ t s) (Q₀ := fun _ _ => True)
      (F := fun s s' => s'.gpr .a0 = KeyGen.zx (s.gpr .a0) ∧ (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp)
      (fun σ s _ h => WP.mono (zxBlk_ok s) fun s' w => ⟨h.zx w, w⟩) (Pack.relct_noMem rfl)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ hg j₁ j₂ f₁ f₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, by rw [f₁.1, f₂.1, KeyGen.zx, KeyGen.zx, hg],
          by rw [f₁.1, KeyGen.zx, KeyGen.zx, zx_set32]⟩
  refine RelCT.seq (R := fun x y => (RS p STK (LeakEq p t) (fun σ s => EP p STK σ t s ∨ EF p STK σ t s) x y ∧ True) ∨
      (RS p STK (LeakEq p t) (EB p STK · t) x y ∧ True)) (RelCT.seq zrel (RelCT.ite ?_ ?_ ?_))
    (relOr (ep_ef_tr hp) (eb_tr hp))
  · rintro x y ⟨_, hg, _⟩
    rw [Steps.eval_nonzero, Steps.eval_nonzero, hg]
  · unfold checks
    refine RelCT.mono (P := RS p STK (LeakEq p t) (KA p STK t)) ?_ (fun x y ⟨⟨h, hg, hz⟩, hb⟩ => ?_) fun _ _ h => h
    · exact RelCT.seq (pieceRS (cntt_piece hP hF hS)) (RelCT.seq (pieceRS kinit_piece)
        (RelCT.seq (zchecks_tr hP hF hS hp ht) (kbranch_tr hF hp ht)))
    · rw [Steps.eval_nonzero] at hb
      obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, i₁, i₂⟩ := h
      have h1 : (x.gpr .a0).setWidth 32 = 1 := by
        rcases i₁.r01 with e | e
        · rw [hz, zx_zero e] at hb; exact absurd hb (by decide)
        · exact e
      have h2 : (y.gpr .a0).setWidth 32 = 1 := hg ▸ h1
      exact ⟨σ₁, σ₂, p₁, p₂, pub, he, ⟨i₁.c, (i₁.ok h1).1, (i₁.ok h1).2⟩, ⟨i₂.c, (i₂.ok h2).1, (i₂.ok h2).2⟩⟩
  · refine RelCT.mono (pieceRS (E := LeakEq p t) (eb_piece (p := p) (STK := STK) (t := t)))
      (fun x y ⟨⟨h, hg, _⟩, hb⟩ => ?_) fun x y h => .inr ⟨h, trivial⟩
    rw [Steps.eval_nonzero] at hb
    have hx0 : x.gpr .a0 = 0 := by simpa using hb
    have h0 : (x.gpr .a0).setWidth 32 = 0 := by rw [hx0]; rfl
    have h0' : (y.gpr .a0).setWidth 32 = 0 := by rw [← hg, hx0]; rfl
    obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, i₁, i₂⟩ := h
    exact ⟨σ₁, σ₂, p₁, p₂, pub, he, ⟨i₁, h0⟩, ⟨i₂, h0'⟩⟩

theorem signLoop_tr :
    RelCT isa (RS p STK (LeakEq p 0) (IK p STK)) (Impl.MlDsa.RISCV64.Sign.signLoop P p) (OX p STK) := by
  unfold Impl.MlDsa.RISCV64.Sign.signLoop
  refine RelCT.seq (pieceRS loopInit_piece) ?_
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y => ∃ t, n = 814 - t ∧ RS p STK (LeakEq p t) (IL p STK · t) x y) (fun n => ?_) 814)
    (fun x y h => ⟨0, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t, hn, hr⟩ e₁ e₂
  have ht : t < 814 := by obtain ⟨_, _, _, _, _, _, i₁, _⟩ := hr; exact i₁.t_lt
  obtain ⟨htr, hz, hc, ho⟩ := iter_tr hP hF hS hp ht _ _ _ _ _ _ hr e₁ e₂
  refine ⟨htr, by rw [Steps.eval_nonzero, Steps.eval_nonzero, hz], fun h => ho ?_, fun h => ⟨814 - (t + 1), by omega_using [hn, ht], t + 1, rfl,
    hc ?_⟩⟩
  · rw [Steps.eval_nonzero] at h; simpa using h
  · rw [Steps.eval_nonzero] at h; simpa using h
end

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-!
# ML-DSA signing on RISC-V: the signature

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/PhaseO.lean`). Once an iteration
passed: `c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r` (in range, as `z`
passed its norm check: `zrange_of_norm`), then `HintBitPack(h)` (with at
most `ω` 1s) to `sig`, which then holds `sigEncode(c̃, z mod± q, h)`
(`output_ok`). Two runs that agree on the hint leak the same (`output_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of polyIs_keepW bytes_keepW
  copyS)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt seqR)
open VG.Impl.MlKem.RISCV64 (copy)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (sigOf)
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem zrange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) :
    ∀ i < n, -((γ - 1 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ (γ : Int) := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [coeff_val h hi]
  simp only [normZq] at this
  omega_arith

/-! ## The hint -/

theorem hintAt_of {m : Mem} {a : Addr} {k : Nat} {f : Nat → Vector Bool n}
    (h : ∀ i < k, HintIs m (a + BitVec.ofNat 64 (1024 * i)) 1 [f i]) :
    hintAt m a k = (List.range k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hn : n = 256 := rfl
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  have ea : coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
    simp only [coeffAt]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega_arith]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = onesSum f k := by
  simp only [hintOnes, onesSum, List.map_map]
  rfl

theorem SL_hint (p : Params) (STK : Nat) (σ : State) (i : Nat) :
    SL p STK σ (5 + i) = SL p STK σ 5 + BitVec.ofNat 64 (1024 * i) := by
  simp only [SL, Lay.A, oP, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega_arith

/-! ## The signature -/

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((Zv p σ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (CTv p σ κ, (List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))

/-- An iteration with counter `κ` passed: `c̃`, `z` and `h`. -/
structure OI (p : Params) (STK : Nat) (σ : State) (κ : Nat) (s : State) : Prop where
  k : IK p STK σ s
  z : ∀ r < p.ℓ, PolyIs s.mem (SL p STK σ (yBase p + r)) (Zv p σ κ r)
  h : ∀ i < p.k, HintIs s.mem (SL p STK σ (5 + i)) 1 [Hv p σ κ i]
  pass : PassV p σ κ
  s4 : s.gpr .s4 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (STK : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  o : OI p STK σ κ s
  sig : bytesAt s.mem ((slay2 p STK σ).A 4 0) (cLen p + zLen p * r) = CTv p σ κ ++ zEnc p σ κ r

/-- A part that writes `W` keeps `OI`. -/
def oiChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  ikChk p STK W && sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (yBase p + 0), 1024 * (p.ℓ - 0)) W &&
    sepAll [scrLen p, STK, p.skLen, 64, p.sigLen] (0, oP (5 + 0), 1024 * (p.k - 0)) W

theorem OI.keep {p : Params} {STK : Nat} {σ : State} {κ : Nat} {s s' : State} (h : OI p STK σ κ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((slay2 p STK σ).RL W) s s') (hc : oiChk p STK W = true) :
    OI p STK σ κ s' := by
  simp only [oiChk, Bool.and_eq_true] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc
  have hL := h.k.sc.site.ok
  have h0 : 0 ∈ sWb2 := by decide
  exact ⟨h.k.keep hk c1, fun r hr => famR_keep hL h0 hk.frame c2 (fun j _ hj => h.z j hj) r (Nat.zero_le _) hr,
    fun i hi => hintIs_keepW hL hk.frame (sepAll_sub c3 (by unfold oP; omega_arith) (by unfold oP; omega_arith)) h0 (h.h i hi),
    h.pass, (hk.cs .s4 (by decide)).trans h.s4⟩

/-- `ssep`, with the checks of the signature. -/
syntax "osep " term:max : tactic
macro_rules
  | `(tactic| osep $hF) => `(tactic| ssep $hF [oiChk, ikChk, sc2Chk, yBase, s1Base, nSec])

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem outCopy_ok {σ : State} {κ : Nat} {s : State} (h : OI p STK σ κ s)
    (hct : bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ κ) :
    WP isa (copy .s11 oCT .s8 0 (cLen p)) s (OS p STK σ κ 0) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hc : 0 < cLen p ∧ cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  refine WP.mono (copyS h.k.sc.site (sb := .s11) (so := oCT) (db := .s8) (dO := 0) (len := cLen p)
    ⟨sptr_ok rfl (by decide), by osep hF⟩ ⟨sptr_ok rfl (by decide), by osep hF⟩ (show ix Reg.s8 ∈ sWb2 by decide)
    (by decide) (by decide) (by omega_arith) hc.1 (by osep hF)) fun s1 ⟨k1, b1⟩ => ⟨h.keep k1 (by osep hF), ?_⟩
  rw [Nat.mul_zero, Nat.add_zero]
  show bytesAt s1.mem (lpa (slay2 p STK σ) (.s8, 0)) (cLen p) = _
  have e : bytesAt s.mem (lpa (slay2 p STK σ) (.s11, oCT)) (cLen p) = CTv p σ κ := hct
  rw [b1, e]
  simp [zEnc]

theorem packZ_ok {σ : State} {κ r : Nat} (hr : r < p.ℓ) {s : State} (h : OS p STK σ κ r s) :
    WP isa (packZ P p r) s (OS p STK σ κ (r + 1)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hz := hF.lz; have hsg := hF.sig
  have hzr := h.o.z r hr
  have hm : zLen p * r + zLen p ≤ zLen p * p.ℓ := by
    have := Nat.mul_le_mul_left (zLen p) (show r + 1 ≤ p.ℓ from hr); rwa [Nat.mul_succ] at this
  have m : KeyGen.BpOk (slay2 p STK σ) sWb2 (yP p r) (p.γ₁ - 1) p.γ₁ (.s8, sigZ p r) (zLen p) :=
    ⟨⟨sptr_ok rfl (by clt hF), by osep hF⟩, ⟨sptr_ok rfl (by clt hF), by osep hF⟩,
      show ix Reg.s8 ∈ sWb2 by decide, by osep hF, hF.zbp, hF.zl, by salsep⟩
  have hpz : normRq [Zv p σ κ r] < p.γ₁ - p.β := h.o.pass.1 r hr
  unfold packZ bitPackAt
  refine KeyGen.bp_ok hP.bitPack h.o.k.sc.site hS m
    hzr.1 (zrange_of_norm hzr hpz (Nat.sub_le _ _)) fun s' k' hb' => ?_
  refine ⟨h.o.keep k' (by osep hF), ?_⟩
  have e0 := bytes_keepW h.o.k.sc.site.ok k'.frame (i := 4) (o := 0) (l := cLen p + zLen p * r) (by osep hF)
    (by decide) (by omega_arith)
  have e1 : polyAt s.mem (lpa (slay2 p STK σ) (yP p r)) = Zv p σ κ r := hzr.2
  rw [e1] at hb'
  have b2 : bytesAt s'.mem ((slay2 p STK σ).A 4 0 + BitVec.ofNat 64 (cLen p + zLen p * r)) (zLen p) =
      bitPack ((Zv p σ κ r).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁ := by
    simp only [lpa, Lay.A, ix, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.zero_add] at hb' ⊢; exact hb'
  rw [Nat.mul_succ, ← Nat.add_assoc, Proof.MlKem.bytesAt_add, e0, h.sig, b2, zEnc, zEnc, List.range_succ,
    List.flatMap_append, List.flatMap_singleton, List.append_assoc]

omit hP hF hS in
theorem hones_ok {σ : State} {κ : Nat} {s : State} (h : OI p STK σ κ s) :
    hintOnes (hintAt s.mem (SL p STK σ 5) p.k) ≤ p.ω := by
  rw [hintAt_of (f := Hv p σ κ) fun i hi => by have := h.h i hi; rwa [SL_hint] at this, hintOnes_map]
  exact h.pass.2.2.2

omit hP hS in
theorem hbp_m {σ : State} : KeyGen.HbpOk (slay2 p STK σ) sWb2 (pS 5) (256 * p.k) p.ω (.s8, sigH p) (p.ω + p.k) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hz := hF.lz; have hsg := hF.sig; have hom := hF.om
  exact ⟨⟨sptr_ok rfl (by decide), by osep hF⟩, ⟨sptr_ok rfl (by clt hF), by osep hF⟩,
    show ix Reg.s8 ∈ sWb2 by decide, by osep hF, by rw [Nat.add_sub_cancel_left]; exact hF.hip, by omega_arith,
    by rw [Nat.add_sub_cancel_left], ⟨by omega_arith, by clt hF, by omega_arith, by omega_arith, by omega_arith⟩, by salsep⟩

theorem hpack_ok {σ : State} {κ : Nat} {s : State} (h : OS p STK σ κ p.ℓ s) :
    WP isa (hintBitPackAt P (Impl.MlDsa.RISCV64.Sign.hP 0) (256 * p.k) p.ω (.s8, sigH p) (p.ω + p.k)) s fun s' =>
      IK p STK σ s' ∧ bytesAt s'.mem ((slay2 p STK σ).A 4 0) p.sigLen = sigV p σ κ ∧ s'.gpr .s4 = 1 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hz := hF.lz; have hsg := hF.sig; have hom := hF.om
  unfold hintBitPackAt
  refine KeyGen.hbp_ok hP.hintBitPack h.o.k.sc.site hS (hbp_m hF)
    (by rw [Nat.add_sub_cancel_left]; exact hones_ok h.o) fun s' k' hb' =>
    ⟨h.o.k.keep k' (by osep hF), ?_, (k'.cs .s4 (by decide)).trans h.o.s4⟩
  have e0 := bytes_keepW h.o.k.sc.site.ok k'.frame (i := 4) (o := 0) (l := cLen p + zLen p * p.ℓ) (by osep hF)
    (by decide) (by omega_arith)
  rw [Nat.add_sub_cancel_left, hintAt_of (f := Hv p σ κ) fun i hi => by
    have := h.o.h i hi; rwa [SL_hint] at this] at hb'
  have b2 : bytesAt s'.mem ((slay2 p STK σ).A 4 0 + BitVec.ofNat 64 (cLen p + zLen p * p.ℓ)) (p.ω + p.k) =
      hintBitPack p.ω p.k ((List.range p.k).map (Hv p σ κ)) := by
    simp only [lpa, Lay.A, ix, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.zero_add] at hb' ⊢; exact hb'
  rw [hF.sig, show sigH p = cLen p + zLen p * p.ℓ from rfl, Proof.MlKem.bytesAt_add, e0, h.sig, b2]
  simp only [sigV, sigOf, sigEncode, zEnc, List.map_map, List.flatMap_map]
  rfl

theorem output_ok {σ : State} {κ : Nat} {s : State} (h : OI p STK σ κ s)
    (hct : bytesAt s.mem ((slay2 p STK σ).A 0 oCT) (cLen p) = CTv p σ κ) :
    WP isa (output P p) s fun s' => IK p STK σ s' ∧ bytesAt s'.mem ((slay2 p STK σ).A 4 0) p.sigLen = sigV p σ κ ∧
      s'.gpr .s4 = 1 := by
  unfold output
  refine WP.seq (WP.mono (outCopy_ok hF h hct) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (wp_seqR (I := fun r => OS p STK σ κ r) p.ℓ 0
    (fun r _ hr s h => packZ_ok hP hF hS (by omega_arith) h) s1 h1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact hpack_ok hP hF hS h2

end

/-! ## Two runs -/

/-- A relational step from each run's correctness and the leaks' equality. -/
theorem liftG {P Q₀ Q : State → State → Prop} {c : Prog isa}
    (hw : ∀ x y, P x y → ∃ A B : State → Prop, WP isa c x A ∧ WP isa c y B ∧ ∀ x' y', A x' → B y' → Q₀ x' y' → Q x' y')
    (ht : RelCT isa P c Q₀) : RelCT isa P c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨A, B, ⟨_, u₁, f₁, a₁⟩, ⟨_, u₂, f₂, b₂⟩, hQ⟩ := hw _ _ hr
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ a₁ b₂ hq⟩

theorem coeff_hint {m : Mem} {a : Addr} {i j : Nat} :
    coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
  simp only [coeffAt]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega_arith]

/-- Two memories holding the same hint have the same coefficients. -/
theorem coeffs_eq {mx my : Mem} {a : Addr} {k : Nat} {F : Nat → Vector Bool n}
    (hx : ∀ i < k, HintIs mx (a + BitVec.ofNat 64 (1024 * i)) 1 [F i])
    (hy : ∀ i < k, HintIs my (a + BitVec.ofNat 64 (1024 * i)) 1 [F i]) :
    (List.range (256 * k)).map (fun c => (coeffAt mx a c).toNat) =
      (List.range (256 * k)).map (fun c => (coeffAt my a c).toNat) := by
  refine List.map_congr_left fun c hc => ?_
  rw [List.mem_range] at hc
  have hi : c / 256 < k := by omega_arith
  have hj : c % 256 < 256 := Nat.mod_lt _ (by decide)
  have e : c = 256 * (c / 256) + c % 256 := (Nat.div_add_mod c 256).symm
  rw [e, coeff_hint, coeff_hint]
  have ex := (hx _ hi).2 0 (by decide) _ hj
  have ey := (hy _ hi).2 0 (by decide) _ hj
  simp only [Nat.mul_zero, Nat.zero_add] at ex ey
  rw [ex, ey]

/-- Two runs that passed, agreeing on the hint. -/
def OR (p : Params) (STK : Nat) (r : Nat) (x y : State) : Prop :=
  ∃ σ₁ σ₂ κ₁ κ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧ OS p STK σ₁ κ₁ r x ∧ OS p STK σ₂ κ₂ r y ∧
    ∀ i < p.k, Hv p σ₁ κ₁ i = Hv p σ₂ κ₂ i

/-- The taint check of the copy of `c̃` to `sig` does not depend on `λ`. -/
theorem copyCt_taint (l : Nat) : (VG.RISCV64.taint.check (Taint.ofRegs [.s8, .s9, .s10, .s11])
    (copy .s11 oCT .s8 0 l)
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s10, .s11]) (copy .s11 oCT .s8 0 32))).isSome =
      true := rfl

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem outCopy_tr :
    RelCT isa (fun x y => ∃ σ₁ σ₂ κ₁ κ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧
      (OI p STK σ₁ κ₁ x ∧ bytesAt x.mem ((slay2 p STK σ₁).A 0 oCT) (cLen p) = CTv p σ₁ κ₁) ∧
      (OI p STK σ₂ κ₂ y ∧ bytesAt y.mem ((slay2 p STK σ₂).A 0 oCT) (cLen p) = CTv p σ₂ κ₂) ∧
      ∀ i < p.k, Hv p σ₁ κ₁ i = Hv p σ₂ κ₂ i) (copy .s11 oCT .s8 0 (cLen p)) (OR p STK 0) := by
  refine liftG (Q₀ := fun _ _ => True) (fun x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, he⟩ => ⟨_, _, outCopy_ok hF h₁.1 h₁.2,
    outCopy_ok hF h₂.1 h₂.2, fun x' y' a b _ => ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, a, b, he⟩⟩) ?_
  exact RelCT.mono (srel2p (I := fun σ s => ∃ κ, OI p STK σ κ s) (fun σ s ⟨_, h⟩ => h.k.sc)
    (copyCt_taint (cLen p))) (fun x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, _⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, pub, ⟨κ₁, h₁.1⟩, ⟨κ₂, h₂.1⟩⟩) fun _ _ h => h

theorem packZ_tr {r : Nat} (hr : r < p.ℓ) : RelCT isa (OR p STK r) (packZ P p r) (OR p STK (r + 1)) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hsh : sigH p = cLen p + zLen p * p.ℓ := rfl
  have hzl : zLen p * p.ℓ ≤ 640 * 7 := Nat.mul_le_mul (by rcases hF.lz with e | e <;> omega_arith) hl.2
  have hcl : cLen p ≤ 64 := by rcases hF.ct with e | e | e <;> omega_arith
  have hz := hF.lz; have hsg := hF.sig
  have m : ∀ σ, KeyGen.BpOk (slay2 p STK σ) sWb2 (yP p r) (p.γ₁ - 1) p.γ₁ (.s8, sigZ p r) (zLen p) := fun σ =>
    have hm : zLen p * r + zLen p ≤ zLen p * p.ℓ := by
      have := Nat.mul_le_mul_left (zLen p) (show r + 1 ≤ p.ℓ from hr); rwa [Nat.mul_succ] at this
    ⟨⟨sptr_ok rfl (by clt hF), by osep hF⟩, ⟨sptr_ok rfl (by clt hF), by osep hF⟩,
      show ix Reg.s8 ∈ sWb2 by decide, by osep hF, hF.zbp, hF.zl, by salsep⟩
  have hrng : ∀ {σ κ x}, OS p STK σ κ r x → Reduced x.mem (lpa (slay2 p STK σ) (yP p r)) ∧
      ∀ i < n, -((p.γ₁ - 1 : Nat) : Int) ≤ modPm (coeffAt x.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ∧
        modPm (coeffAt x.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ≤ (p.γ₁ : Int) := fun h =>
    ⟨(h.o.z r hr).1, zrange_of_norm (h.o.z r hr) (h.o.pass.1 r hr) (Nat.sub_le _ _)⟩
  refine liftG (Q₀ := fun _ _ => True) (fun x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, he⟩ => ⟨_, _, packZ_ok hP hF hS hr h₁,
    packZ_ok hP hF hS hr h₂, fun x' y' a b _ => ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, a, b, he⟩⟩) ?_
  unfold packZ bitPackAt
  refine RelCT.mono (RelCT.exists_ fun σ => KeyGen.bp_tr hP.bitPack hS (m σ)
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      (Reduced x.mem (lpa (slay2 p STK σ) (yP p r)) ∧
        ∀ i < n, -((p.γ₁ - 1 : Nat) : Int) ≤ modPm (coeffAt x.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ∧
          modPm (coeffAt x.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ≤ (p.γ₁ : Int)) ∧
      (Reduced y.mem (lpa (slay2 p STK σ) (yP p r)) ∧
        ∀ i < n, -((p.γ₁ - 1 : Nat) : Int) ≤ modPm (coeffAt y.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ∧
          modPm (coeffAt y.mem (lpa (slay2 p STK σ) (yP p r)) i).toNat q ≤ (p.γ₁ : Int)))
    fun x y ⟨T, hx, hy⟩ => ⟨T.1, T.2.1, T.2.2, hx.1, hy.1, hx.2, hy.2⟩)
    (fun x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, _⟩ => ⟨σ₁, sc2_twoL pub h₁.o.k.sc h₂.o.k.sc, hrng h₁,
      by rw [slay2_pub pub]; exact hrng h₂⟩) fun _ _ h => h


theorem hpack_tr :
    RelCT isa (OR p STK p.ℓ) (hintBitPackAt P (Impl.MlDsa.RISCV64.Sign.hP 0) (256 * p.k) p.ω (.s8, sigH p) (p.ω + p.k))
      fun _ _ => True := by
  unfold hintBitPackAt
  refine RelCT.mono (RelCT.exists_ fun σ => KeyGen.hbp_tr hP.hintBitPack hS (hbp_m hF (σ := σ))
    (P := fun x y => Two (slay2 p STK σ) sWb2 STK x y ∧
      hintOnes (hintAt x.mem (SL p STK σ 5) p.k) ≤ p.ω ∧ hintOnes (hintAt y.mem (SL p STK σ 5) p.k) ≤ p.ω ∧
      (List.range (256 * p.k)).map (fun c => (coeffAt x.mem (SL p STK σ 5) c).toNat) =
        (List.range (256 * p.k)).map (fun c => (coeffAt y.mem (SL p STK σ 5) c).toNat))
    fun x y ⟨T, ox, oy, e⟩ => ⟨T.1, T.2.1, T.2.2, by rw [Nat.add_sub_cancel_left]; exact ox,
      by rw [Nat.add_sub_cancel_left]; exact oy, e⟩) ?_ fun _ _ h => h
  rintro x y ⟨σ₁, σ₂, κ₁, κ₂, p₁, p₂, pub, h₁, h₂, he⟩
  refine ⟨σ₁, sc2_twoL pub h₁.o.k.sc h₂.o.k.sc, hones_ok h₁.o, by rw [SL_pub pub]; exact hones_ok h₂.o,
    coeffs_eq (F := Hv p σ₁ κ₁) (fun i hi => by have := h₁.o.h i hi; rwa [SL_hint] at this) fun i hi => ?_⟩
  have := h₂.o.h i hi
  rw [SL_hint, ← SL_pub pub, ← he i hi] at this
  exact this

/-- Two runs that passed, and agree on the hint, leak the same. -/
theorem output_tr :
    RelCT isa (fun x y => ∃ σ₁ σ₂ κ₁ κ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧
      (OI p STK σ₁ κ₁ x ∧ bytesAt x.mem ((slay2 p STK σ₁).A 0 oCT) (cLen p) = CTv p σ₁ κ₁) ∧
      (OI p STK σ₂ κ₂ y ∧ bytesAt y.mem ((slay2 p STK σ₂).A 0 oCT) (cLen p) = CTv p σ₂ κ₂) ∧
      ∀ i < p.k, Hv p σ₁ κ₁ i = Hv p σ₂ κ₂ i) (output P p) fun _ _ => True := by
  unfold output
  refine RelCT.seq (outCopy_tr hF) (RelCT.seq ?_ (hpack_tr hP hF hS))
  simpa using rr_seqR (R := fun r => OR p STK r) p.ℓ 0 fun r _ hr => packZ_tr hP hF hS (by omega_arith)
end

end VG.Proof.MlDsa.RISCV64.Sign
