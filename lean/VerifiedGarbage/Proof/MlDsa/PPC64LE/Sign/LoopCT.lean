module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Loop
import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Loop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA signing on PPC64LE: the loop leaks what `signLeakT` says

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/PhaseLCT.lean`): two runs whose
remaining iterations leak the same (`LeakEq`) agree on the iteration's `c̃`
(`leq_ct`), on whether it passes (`leq_pass`) and on its hint if it does
(`leq_hints`), and, if it is rejected, on what the rest leaks (`leq_succ`);
so they agree on the branches of each iteration, and leak the same
(`iter_tr`, `signLoop_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (signLeakLoopT leakT_step outTag amat ParamsOk signCommit_eq)
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
  signLeakLoopT p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
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
    signLeakLoopT p maxBounds (amat p (Am p σ₁)) ((List.range p.ℓ).map (S1v p σ₁)) ((List.range p.k).map (S2v p σ₁))
      ((List.range p.k).map (T0v p σ₁)) (muOf σ₁) (rppOf p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoopT p maxBounds (amat p (Am p σ₂)) ((List.range p.ℓ).map (S1v p σ₂)) ((List.range p.k).map (S2v p σ₂))
      ((List.range p.k).map (T0v p σ₂)) (muOf σ₂) (rppOf p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega]; exact h

theorem leq_ct (h : LeakEq p t σ₁ σ₂) (ht : t < 814) : CTv p σ₁ (p.ℓ * t) = CTv p σ₂ (p.ℓ * t) := by
  have := (leakT_step (leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakT_step (leq_step h ht)).2.1 hr).2
  unfold LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega, Nat.mul_succ]
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
  have e := (leakT_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂] at e
  by_cases h1 : PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [ifp h1, ifn h2] at e; cases e
  · rw [ifn h1, ifp h2] at e; cases e
  · exact iff_of_false h1 h2

theorem leq_hints (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome)
    (h1 : PassV p σ₁ (p.ℓ * t)) (h2 : PassV p σ₂ (p.ℓ * t)) :
    (List.range p.k).map (Hv p σ₁ (p.ℓ * t)) = (List.range p.k).map (Hv p σ₂ (p.ℓ * t)) := by
  have e := (leakT_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂, ifp h1, ifp h2] at e
  exact hints_inj (by simp) (List.cons.inj e).2

end

end VG.Proof.MlDsa.PPC64LE.Sign
