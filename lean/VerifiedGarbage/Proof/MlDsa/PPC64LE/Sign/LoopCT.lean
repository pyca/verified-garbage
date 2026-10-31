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
      ite_true, ite_false] at h <;> first | omega | (simp_all <;> omega)

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
    exact ⟨fun r hr => iff_of_true (fun j hj => h1.1 j (by omega)) (fun j hj => h2.1 j (by omega)),
      fun i hi => iff_of_true ⟨h1.1, fun j hj => h1.2.1 j (by omega)⟩ ⟨h2.1, fun j hj => h2.2.1 j (by omega)⟩, hpass⟩
  · have h2 : ¬ PassV p σ₂ (p.ℓ * t) := fun h2 => h1 (hpass.mpr h2)
    have e := leakF_tag (leq_step h ht) (iter_rej hp hs₁ h1) (iter_rej hp hs₂ h2)
    rw [tag_eq hp hs₁, tag_eq hp hs₂] at e
    obtain ⟨ea, ex, eab, ey⟩ := tagFn_eq e
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

/-! ## An iteration -/

/-- The loop ended in both runs: they agree on whether it succeeded, and if it did, on the hint. -/
def OX (p : Params) (STK : Nat) (x y : State) : Prop :=
  ∃ σ₁ σ₂, SPre p STK σ₁ ∧ SPre p STK σ₂ ∧ sPub p σ₁ σ₂ ∧ XS p STK σ₁ x ∧ XS p STK σ₂ y ∧
    x.gpr .r24 = y.gpr .r24 ∧ (x.gpr .r24 = 1 → ∃ f : Nat → Vector Bool n,
      (∀ i < p.k, HintIs x.mem (SL p STK σ₁ (5 + i)) 1 [f i]) ∧ ∀ i < p.k, HintIs y.mem (SL p STK σ₁ (5 + i)) 1 [f i])

/-- After iteration `t` of two runs: both continue, leaking the same from then on, or both end. -/
def IX (p : Params) (STK : Nat) (t : Nat) (x y : State) : Prop :=
  x.gpr .r25 = y.gpr .r25 ∧ (x.gpr .r25 ≠ 0 → RS p STK (LeakEq p (t + 1)) (IL p STK · (t + 1)) x y) ∧
    (x.gpr .r25 = 0 → OX p STK x y)

theorem LP.il {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : LP p STK σ t s) (hz : s.gpr .r25 ≠ 0) :
    IL p STK σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h hz

theorem LP.xs {p : Params} {STK : Nat} {σ : State} {t : Nat} {s : State} (h : LP p STK σ t s) (hz : s.gpr .r25 = 0) :
    XS p STK σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd hz h
  · exact h

/-- The taint check of `κ ← κ + ℓ` does not depend on `ℓ`. -/
theorem kapAdd_taint (l : Nat) : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) (.block [.addi .r27 .r27 l])
    (VG.Taint.hintOf VG.PPC64LE.taint (Taint.ofRegs [.r31]) (.block [.addi .r27 .r27 4]))).isSome = true := rfl

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
    (heq:∀ x y,RS p STK E I x y→x.gpr .r24=y.gpr .r24)
    (ha:RelCT isa (RS p STK E fun σ s=>I σ s ∧ s.gpr .r24≠0) a Q)
    (hb:RelCT isa (RS p STK E fun σ s=>I σ s ∧ s.gpr .r24=0) b Q) :
    RelCT isa (RS p STK E I) (ifOkElse a b) Q := by
  refine RelCT.ite (fun x y h=>by rw [eval_nonzero,eval_nonzero,heq x y h]) ?_ ?_
  · refine RelCT.mono ha (fun x y ⟨h,hb⟩=>?_) (fun _ _ h=>h)
    have hx:x.gpr .r24≠0:=by rw [eval_nonzero] at hb; simpa using hb
    obtain ⟨σ,τ,p₁,p₂,pub,he,h₁,h₂⟩:=h
    exact ⟨σ,τ,p₁,p₂,pub,he,⟨h₁,hx⟩,⟨h₂,(heq x y ⟨σ,τ,p₁,p₂,pub,he,h₁,h₂⟩) ▸ hx⟩⟩
  · refine RelCT.mono hb (fun x y ⟨h,hb⟩=>?_) (fun _ _ h=>h)
    have hx:x.gpr .r24=0:=by rw [eval_nonzero] at hb; simpa using hb
    obtain ⟨σ,τ,p₁,p₂,pub,he,h₁,h₂⟩:=h
    exact ⟨σ,τ,p₁,p₂,pub,he,⟨h₁,hx⟩,⟨h₂,(heq x y ⟨σ,τ,p₁,p₂,pub,he,h₁,h₂⟩) ▸ hx⟩⟩

theorem seqOk_RS {E : State→State→Prop} {I : Nat→State→State→Prop} {f : Nat→Prog isa} :
    ∀ (n a : Nat),
      (∀ k,a<k→k≤a+n→∀ x y,RS p STK E (I k) x y→x.gpr .r24=y.gpr .r24) →
      (∀ k,a≤k→k<a+n→RelCT isa (RS p STK E (I k)) (f k) (RS p STK E (I (k+1)))) →
      RelCT isa (RS p STK E (I a)) (seqOk f a n)
        (RS p STK E fun σ s=>∃k,a≤k ∧ k≤a+n ∧ I k σ s ∧ (k=a+n ∨ s.gpr .r24=0))
  | 0,a,_,_=>RelCT.mono (nil_tr (fun _ _ h=>h)) (fun _ _ h=>h) fun _ _ h=>
      h.mono (fun _ _ hi=>⟨a,Nat.le_refl _,by omega,hi,.inl (by omega)⟩)
  | n+1,a,hq,h=>by
    rw [seqOk]
    refine RelCT.seq (h a (Nat.le_refl _) (by omega)) ?_
    refine ifOkElse_RS (hq (a+1) (by omega) (by omega)) ?_ ?_
    · refine RelCT.mono (seqOk_RS n (a+1) (fun k hk hk'=>hq k (by omega) (by omega))
        (fun k hk hk'=>h k (by omega) (by omega))) (fun _ _ hi=>hi.mono fun _ _ hi=>hi.1) ?_
      intro _ _ hi
      exact hi.mono fun _ _ ⟨k,hk,hk',hi,hd⟩=>⟨k,by omega,by omega,hi,hd.imp (fun _=>by omega) id⟩
    · exact nil_tr fun _ _ hi=>hi.mono fun _ _ ⟨hi,hz⟩=>⟨a+1,by omega,by omega,hi,.inr hz⟩

end

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
  (hp : ParamsOk p)
include hP hF hS hp

omit hP hF hS in
theorem ep_ef_tr {t : Nat} :
    RelCT isa (fun x y => RS p STK (LeakEq p t) (fun σ s => EP p STK σ t s ∨ EF p STK σ t s) x y ∧ True)
      (.block [.subi .r25 .r25 1]) (IX p STK t) := by
  refine liftQ (J := fun σ s => LP p STK σ t s) (F := fun s s' => W1 .r25 (s.gpr .r25 - BitVec.ofNat 64 1) s s')
    (fun σ s _ h => WP.conj (dec_end hp (h.elim .inl (.inr ∘ .inl))) (subi_ok (by decide) (by decide) s))
    (RelCT.mono (srel2 (I := fun σ s => EP p STK σ t s ∨ EF p STK σ t s) (fun σ s h => h.elim (·.k.sc) (·.k.sc))
      (by taint_decide)) (fun _ _ h => h.1.rel2) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ w₁ w₂ _
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.gpr .r25 = 0 := by rw [w₁.1, e₁.r25]; decide
    have zy : y'.gpr .r25 = 0 := by rw [w₂.1, e₂.r25]; decide
    have r₁ : x'.gpr .r24 = 1 := by rw [w₁.2.1 .r24 (by decide)]; exact e₁.r24
    have r₂ : y'.gpr .r24 = 1 := by rw [w₂.2.1 .r24 (by decide)]; exact e₂.r24
    refine ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨σ₁, σ₂, p₁, p₂, hpub, j₁.xs zx, j₂.xs zy, by rw [r₁, r₂],
      fun _ => ⟨Hv p σ₁ (p.ℓ * t), fun i hi => by rw [w₁.2.2.1]; exact e₁.h i hi, fun i hi => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) i (List.mem_range.mpr hi),
      w₂.2.2.1, SL_pub hpub]
    exact e₂.h i hi
  · exact absurd ((leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.gpr .r25 = y'.gpr .r25 := by rw [w₁.1, w₂.1, f₁.r25, f₂.r25]
    have r₁ : x'.gpr .r24 = 0 := by rw [w₁.2.1 .r24 (by decide)]; exact f₁.r24
    have r₂ : y'.gpr .r24 = 0 := by rw [w₂.2.1 .r24 (by decide)]; exact f₂.r24
    refine ⟨zxy, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, leq_succ he f₁.t_lt ⟨_, iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, j₁.xs h, j₂.xs (zxy ▸ h), by rw [r₁, r₂],
      fun h1 => absurd (h1.symm.trans r₁) (by decide)⟩⟩

omit hP hF hS in
theorem eb_tr {t : Nat} :
    RelCT isa (fun x y => RS p STK (LeakEq p t) (fun σ s => EB p STK σ t s) x y ∧ True)
      (.block [.subi .r25 .r25 1]) (IX p STK t) := by
  refine liftQ (J := fun σ s => LP p STK σ t s) (F := fun s s' => W1 .r25 (s.gpr .r25 - BitVec.ofNat 64 1) s s')
    (fun σ s _ h => WP.conj (dec_end hp (.inr (.inr h))) (subi_ok (by decide) (by decide) s))
    (RelCT.mono (srel2 (I := fun σ s => EB p STK σ t s) (fun σ s h => h.k.sc) (by taint_decide))
      (fun _ _ h => h.1.rel2) fun _ _ h => h) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ w₁ w₂ _
  have zx : x'.gpr .r25 = 0 := by rw [w₁.1, e₁.r25]; decide
  have zy : y'.gpr .r25 = 0 := by rw [w₂.1, e₂.r25]; decide
  have r₁ : x'.gpr .r24 = 0 := by rw [w₁.2.1 .r24 (by decide)]; exact e₁.r24
  have r₂ : y'.gpr .r24 = 0 := by rw [w₂.2.1 .r24 (by decide)]; exact e₂.r24
  exact ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨σ₁, σ₂, p₁, p₂, hpub, j₁.xs zx, j₂.xs zy, by rw [r₁, r₂],
    fun h1 => absurd (h1.symm.trans r₁) (by decide)⟩⟩


omit hP hF hS hp in
theorem kthen_piece {t : Nat} :
    SPiece p STK (fun σ s => KO p STK σ t s ∧ s.gpr .r24 ≠ 0) (EP p STK · t) (.block [.li .r25 1]) :=
  ⟨fun σ s _ h => kthen_ok h.1 h.2, srel2 (fun σ s h => h.1.b.l.k.sc) (by taint_decide)⟩

omit hP hS hp in
theorem kelse_piece {t : Nat} :
    SPiece p STK (fun σ s => KO p STK σ t s ∧ s.gpr .r24 = 0) (EF p STK · t) (.block [.addi .r27 .r27 p.ℓ]) :=
  ⟨fun σ s _ h => kelse_ok (by have := hF.l; omega) h.1 h.2, srel2 (fun σ s h => h.1.b.l.k.sc) (kapAdd_taint p.ℓ)⟩

omit hP hF hS hp in
theorem eb_piece {t : Nat} :
    SPiece p STK (fun σ s => IB p STK σ t s ∧ (s.gpr .r3).setWidth 32 = 0) (EB p STK · t)
      (.block [.li .r24 0, .li .r25 1]) :=
  ⟨fun σ s _ h => eb_ok h.1 h.2, srel2 (fun σ s h => h.1.c.1.l.k.sc) (by taint_decide)⟩

omit hP hF hS hp in
theorem loopInit_piece : SPiece p STK (IK p STK) (IL p STK · 0) (.block [.li .r27 0, .li .r25 814]) :=
  ⟨fun σ s _ h => loopInit_ok h, srel2 (fun σ s h => h.sc) (by taint_decide)⟩

omit hp in
theorem ballRS_tr {t : Nat} (ht : t < 814) :
    RelCT isa (RS p STK (LeakEq p t) (ICd p STK t)) (ballAt P (cLen p) p.τ cP)
      (fun x y => RS p STK (LeakEq p t) (IB p STK · t) x y ∧ (x.gpr .r3).setWidth 32 = (y.gpr .r3).setWidth 32) := by
  refine RelCT.mono (liftQ (G := fun _ _ => True) (J := fun σ s => IB p STK σ t s) (F := fun _ _ => True)
    (Q₀ := fun x y => (x.gpr .r3).setWidth 32 = (y.gpr .r3).setWidth 32)
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
    RelCT isa (RS p STK (LeakEq p t) (KO p STK · t)) (ifOkElse (.block [.li .r25 1]) (.block [.addi .r27 .r27 p.ℓ]))
      (fun x y => (RS p STK (LeakEq p t) (fun σ s => EP p STK σ t s ∨ EF p STK σ t s) x y ∧ True) ∨
        (RS p STK (LeakEq p t) (EB p STK · t) x y ∧ True)) := by
  have e24 : ∀ x y, RS p STK (LeakEq p t) (KO p STK · t) x y → x.gpr .r24 = y.gpr .r24 :=
    fun x y ⟨σ₁, σ₂, _, _, _, he, h₁, h₂⟩ => by
      rw [h₁.r24, h₂.r24]; exact bit_congr (leq_pass hp he ht h₁.b.some h₂.b.some)
  refine RelCT.ite (fun x y h => by rw [eval_nonzero, eval_nonzero, e24 x y h]) ?_ ?_
  · refine RelCT.mono (pieceRS (E := LeakEq p t) (kthen_piece (p := p) (STK := STK) (t := t)))
      (fun x y ⟨h, hb⟩ => ?_) fun x y h => .inl ⟨RS.mono h fun _ _ h => .inl h, trivial⟩
    have hx : x.gpr .r24 ≠ 0 := by rw [eval_nonzero] at hb; simpa using hb
    obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, h₁, h₂⟩ := h
    exact ⟨σ₁, σ₂, p₁, p₂, pub, he, ⟨h₁, hx⟩, ⟨h₂, (e24 x y ⟨σ₁, σ₂, p₁, p₂, pub, he, h₁, h₂⟩) ▸ hx⟩⟩
  · refine RelCT.mono (pieceRS (E := LeakEq p t) (kelse_piece hF (STK := STK) (t := t)))
      (fun x y ⟨h, hb⟩ => ?_) fun x y h => .inl ⟨RS.mono h fun _ _ h => .inr h, trivial⟩
    have hx : x.gpr .r24 = 0 := by rw [eval_nonzero] at hb; simpa using hb
    obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, h₁, h₂⟩ := h
    exact ⟨σ₁, σ₂, p₁, p₂, pub, he, ⟨h₁, hx⟩, ⟨h₂, (e24 x y ⟨σ₁, σ₂, p₁, p₂, pub, he, h₁, h₂⟩) ▸ hx⟩⟩


theorem checksR0_tr {t:Nat} (ht:t<814) :
    RelCT isa (RS p STK (LeakEq p t) fun σ s=>IQ p STK σ t 0 0 s) (checksR0 P p)
      (RS p STK (LeakEq p t) (KO p STK · t)) := by
  unfold checksR0
  refine RelCT.seq (seqOk_RS (I:=fun i σ s=>IQ p STK σ t i i s) p.k 0
    (fun i _ hi x y ⟨σ,τ,_,_,_,he,h₁,h₂⟩=>by
      rw [h₁.r24,h₂.r24];exact bit_congr ((leq_agree hp he ht h₁.b.some h₂.b.some).2.1 i (by omega)))
    (fun i _ hi=>pieceRS (r0R_piece hP hF hS (by omega)))) ?_
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
      rw [h₁.r24,h₂.r24];exact bit_congr ((leq_agree hp he ht h₁.b.some h₂.b.some).1 i (by omega)))
    (fun i _ hi=>pieceRS (zR_piece hP hF hS (by omega)))) ?_
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
  refine RelCT.seq (R := fun x y => (RS p STK (LeakEq p t) (fun σ s => EP p STK σ t s ∨ EF p STK σ t s) x y ∧ True) ∨
      (RS p STK (LeakEq p t) (EB p STK · t) x y ∧ True)) (RelCT.ite ?_ ?_ ?_)
    (relOr (ep_ef_tr hp) (eb_tr hp))
  · rintro x y ⟨_, hg⟩
    rw [eval_nonzero_w, eval_nonzero_w, hg]
  · unfold checks
    refine RelCT.mono (P := RS p STK (LeakEq p t) (KA p STK t)) ?_ (fun x y ⟨⟨h, hg⟩, hb⟩ => ?_) fun _ _ h => h
    · exact RelCT.seq (pieceRS (cntt_piece hP hF hS)) (RelCT.seq (pieceRS kinit_piece)
        (RelCT.seq (zchecks_tr hP hF hS hp ht) (kbranch_tr hF hp ht)))
    · rw [eval_nonzero_w] at hb
      obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, i₁, i₂⟩ := h
      have h1 : (x.gpr .r3).setWidth 32 = 1 := by
        rcases i₁.r01 with e | e
        · rw [e] at hb; exact absurd hb (by decide)
        · exact e
      have h2 : (y.gpr .r3).setWidth 32 = 1 := hg ▸ h1
      exact ⟨σ₁, σ₂, p₁, p₂, pub, he, ⟨i₁.c, (i₁.ok h1).1, (i₁.ok h1).2⟩, ⟨i₂.c, (i₂.ok h2).1, (i₂.ok h2).2⟩⟩
  · refine RelCT.mono (pieceRS (E := LeakEq p t) (eb_piece (p := p) (STK := STK) (t := t)))
      (fun x y ⟨⟨h, hg⟩, hb⟩ => ?_) fun x y h => .inr ⟨h, trivial⟩
    rw [eval_nonzero_w] at hb
    have h0 : (x.gpr .r3).setWidth 32 = 0 := by simpa using hb
    obtain ⟨σ₁, σ₂, p₁, p₂, pub, he, i₁, i₂⟩ := h
    exact ⟨σ₁, σ₂, p₁, p₂, pub, he, ⟨i₁, h0⟩, ⟨i₂, hg ▸ h0⟩⟩

theorem signLoop_tr :
    RelCT isa (RS p STK (LeakEq p 0) (IK p STK)) (Impl.MlDsa.PPC64LE.Sign.signLoop P p) (OX p STK) := by
  unfold Impl.MlDsa.PPC64LE.Sign.signLoop
  refine RelCT.seq (pieceRS loopInit_piece) ?_
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y => ∃ t, n = 814 - t ∧ RS p STK (LeakEq p t) (IL p STK · t) x y) (fun n => ?_) 814)
    (fun x y h => ⟨0, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t, hn, hr⟩ e₁ e₂
  have ht : t < 814 := by obtain ⟨_, _, _, _, _, _, i₁, _⟩ := hr; exact i₁.t_lt
  obtain ⟨htr, hz, hc, ho⟩ := iter_tr hP hF hS hp ht _ _ _ _ _ _ hr e₁ e₂
  refine ⟨htr, by rw [eval_nonzero, eval_nonzero, hz], fun h => ho ?_, fun h => ⟨814 - (t + 1), by omega, t + 1, rfl,
    hc ?_⟩⟩
  · rw [eval_nonzero] at h; simpa using h
  · rw [eval_nonzero] at h; simpa using h
end

end VG.Proof.MlDsa.PPC64LE.Sign
