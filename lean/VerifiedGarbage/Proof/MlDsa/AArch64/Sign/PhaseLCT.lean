module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseL
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseL
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD

/-!
# ML-DSA signing on AArch64: what runs whose loops leak the same agree on

Two runs whose remaining iterations leak the same (`LeakEq`) agree on the
iteration's `c̃` (`leq_ct`), on whether it passes (`leq_pass`) and on its hint
if it does (`leq_hints`), and, if it is rejected, on what the rest leaks
(`leq_succ`); so they agree on the branches of each iteration.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

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
  rw [show 999 - t + 1 = 1000 - t by omega]; exact h

theorem leq_ct (h : LeakEq p t σ₁ σ₂) (ht : t < 814) : CTv p σ₁ (p.ℓ * t) = CTv p σ₂ (p.ℓ * t) := by
  have := (leakF_step (leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakF_step (leq_step h ht)).2.1 hr).2
  unfold LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega, Nat.mul_succ]
  exact this

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat} (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
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

/-- What the branches of the checks need two runs to agree on: whether the
first `r` polynomials of `z` passed, for each `r` (the checks stop at the
first that fails), whether `z` and the first `i` polynomials of `r₀` passed,
for each `i`, and whether the iteration passed. -/
abbrev PrefixChecksAgree (p : Params) (t : Nat) (σ₁ σ₂ : State) : Prop :=
  (∀ r ≤ p.ℓ, (∀ j < r, normRq [Zv p σ₁ (p.ℓ * t) j] < p.γ₁ - p.β) ↔
    (∀ j < r, normRq [Zv p σ₂ (p.ℓ * t) j] < p.γ₁ - p.β)) ∧
  (∀ i ≤ p.k, (ZOk p σ₁ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ₁ (p.ℓ * t) j] < p.γ₂ - p.β) ↔
    (ZOk p σ₂ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ₂ (p.ℓ * t) j] < p.γ₂ - p.β)) ∧
  (PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t))

/-- `signRejectTag`'s value: which check failed, and for those of `z` and
`r₀` the first polynomial that failed it. -/
def prefixTagFn (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] (x y : Nat) : Nat :=
  if ¬ a then 5 * x else if ¬ b then 2 + 5 * y else if ¬ c then 3 else 4

theorem prefixTagFn_eq {a b c a' b' c' : Prop} [Decidable a] [Decidable b] [Decidable c] [Decidable a'] [Decidable b']
    [Decidable c'] {x y x' y' : Nat} (h : prefixTagFn a b c x y = prefixTagFn a' b' c' x' y') :
    (a ↔ a') ∧ (¬ a → x = x') ∧ (a ∧ b ↔ a' ∧ b') ∧ (a → ¬ b → y = y') := by
  unfold prefixTagFn at h
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases ha' : a' <;> by_cases hb' : b' <;>
    by_cases hc' : c' <;> simp only [ha, hb, hc, ha', hb', hc', not_true_eq_false, not_false_eq_true,
      ite_true, ite_false] at h <;> first | omega | (simp_all <;> omega)

/-- The first polynomial of `z` that fails its check, or `ℓ`. -/
abbrev zFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.ℓ).findIdx fun r => decide (normRq [Zv p σ κ r] ≥ p.γ₁ - p.β)

/-- The first polynomial of `r₀` that fails its check, or `k`. -/
abbrev rFirst (p : Params) (σ : State) (κ : Nat) : Nat :=
  (List.range p.k).findIdx fun i => decide (normRq [R0v p σ κ i] ≥ p.γ₂ - p.β)

theorem prefixTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat}
    (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    signRejectTag p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
      ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) κ =
      prefixTagFn (ZOk p σ κ) (R0Ok p σ κ) (∀ j < p.k, normRq [CT0v p σ κ j] < p.γ₂) (zFirst p σ κ) (rFirst p σ κ) := by
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
theorem leq_prefixAgree (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) : PrefixChecksAgree p t σ₁ σ₂ := by
  have hpass := leq_pass hp h ht hs₁ hs₂
  by_cases h1 : PassV p σ₁ (p.ℓ * t)
  · have h2 := hpass.mp h1
    exact ⟨fun r hr => iff_of_true (fun j hj => h1.1 j (by omega)) (fun j hj => h2.1 j (by omega)),
      fun i hi => iff_of_true ⟨h1.1, fun j hj => h1.2.1 j (by omega)⟩ ⟨h2.1, fun j hj => h2.2.1 j (by omega)⟩, hpass⟩
  · have h2 : ¬ PassV p σ₂ (p.ℓ * t) := fun h2 => h1 (hpass.mpr h2)
    have e := leakF_tag (leq_step h ht) (iter_rej hp hs₁ h1) (iter_rej hp hs₂ h2)
    rw [prefixTag_eq hp hs₁, prefixTag_eq hp hs₂] at e
    obtain ⟨ea, ex, eab, ey⟩ := prefixTagFn_eq e
    refine ⟨fun r hr => ?_, fun i hi => ?_, hpass⟩
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · exact iff_of_true (fun j hj => hz j (by omega)) (fun j hj => ea.mp hz j (by omega))
      · rw [prefix_ok _ hr, prefix_ok _ hr]; exact iff_of_eq (congrArg (r ≤ ·) (ex hz))
    · by_cases hz : ZOk p σ₁ (p.ℓ * t)
      · have hz' := ea.mp hz
        by_cases hr0 : R0Ok p σ₁ (p.ℓ * t)
        · have hr0' := (eab.mp ⟨hz, hr0⟩).2
          exact iff_of_true ⟨hz, fun j hj => hr0 j (by omega)⟩ ⟨hz', fun j hj => hr0' j (by omega)⟩
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

/-! ## Pieces from runs related through their entry states -/

section
variable {p : Params} {D : Nat}

/-- A piece that takes each run from `I` to `J` (and `s` to `s'` with `F s s'`), and leaks the same from runs
related by `RS p D E I` and `G`, with `Q₀` of the final states. -/
theorem liftQ {E I J G Q₀ Q F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (fun x y => RS p D E I x y ∧ G x y) c Q₀)
    (hQ : ∀ σ₁ σ₂ x y x' y', (signK p D).pre σ₁ → (signK p D).pre σ₂ → (signK p D).pub σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → G x y → J σ₁ x' → J σ₂ y' → F x x' → F y y' → Q₀ x' y' → Q x' y') :
    RelCT isa (fun x y => RS p D E I x y ∧ G x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩ := hr
  obtain ⟨_, u₁, f₁, j₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, j₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ _ _ _ _ p₁ p₂ hpub he i₁ i₂ hg j₁ j₂ g₁ g₂ hq⟩

theorem relOr {P₁ P₂ Q : State → State → Prop} {c : Prog isa} (h₁ : RelCT isa P₁ c Q) (h₂ : RelCT isa P₂ c Q) :
    RelCT isa (fun x y => P₁ x y ∨ P₂ x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  rcases hr with h | h
  exacts [h₁ _ _ _ _ _ _ h e₁ e₂, h₂ _ _ _ _ _ _ h e₁ e₂]

end

theorem x9_ne {s : State} (h : isa.eval (.nonzero .x .x9) s = some true) : s.gpr .x9 ≠ 0 := by
  rw [eval_x9] at h; simpa using h

theorem x9_zero {s : State} (h : isa.eval (.nonzero .x .x9) s = some false) : s.gpr .x9 = 0 := by
  rw [eval_x9] at h; simpa using h

/-! ## An iteration -/

section
variable {p : Params} {D : Nat}

theorem x0_one {s : State} (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1)
    (hb : isa.eval (.nonzero .w .x0) s = some true) : (s.gpr .x0).setWidth 32 = 1 := by
  rw [eval_w0] at hb
  rcases hr with h | h
  · rw [h] at hb; cases hb
  · exact h

theorem x0_zero {s : State} (hb : isa.eval (.nonzero .w .x0) s = some false) : (s.gpr .x0).setWidth 32 = 0 := by
  rw [eval_w0] at hb; simpa using hb

end

end VG.Proof.MlDsa.AArch64.Sign
