module
public import VerifiedGarbage.Spec.MlDsa.Contract

import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ML-DSA: what signing leaks, iteration by iteration

`signLeakLoop` (`Spec/MlDsa/Contract.lean`) lists the commitment hash `c̃`
of each iteration of the signing loop, then the hint of the one that
passes. That list does not determine where each iteration ends: after a
`c̃`, a rejected iteration continues with the next `c̃` (`λ/4` numbers),
the passing one ends with its hint (`256k` numbers of 0 and 1), and one
whose `SampleInBall` does not finish ends the list. As `256k = 32 · λ/4`
in every parameter set, a hint of an iteration that passes reads as the
`c̃`s of 32 more iterations, the last of which does not finish, whenever
those `c̃`s consist of 0s and 1s that match the hint. Two runs with such
inputs agree on `signLeak` but run different numbers of iterations, so no
implementation that stops when its loop does meets `signContract`'s
constant-time obligation for them (they exist, as far as anyone can tell,
though no one can find them).

`signLeakLoopT` is the same list with a number after each `c̃` that says
how the iteration ended (the check that rejected it, `signRejectTag`, which
is never 1; 1: passed; nothing: `SampleInBall` did not finish), which
determines the structure of the loop: two runs that agree on it agree on
each `c̃`, on the outcome of each iteration and on the hint of the one that
passes (`leakT_step`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

/-- `signRejectTag` without the polynomial: 0, 2, 3 or 4, the check that
rejects the iteration, which is all an implementation that runs each check
on all its polynomials reveals. -/
def signRejectTagC (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) (κ : Nat) : Nat :=
  let (y, w, ctilde) := signCommit p Â μ ρ'' κ
  match sampleInBall p.τ b.ball ctilde with
  | none => 0
  | some c =>
    let ĉ := ntt (toRq c)
    let z := addVec (y.map toRq) (ŝ₁.map fun s => nttInv (multiplyNTT ĉ s))
    let r₀ := (subVec w (ŝ₂.map fun s => nttInv (multiplyNTT ĉ s))).map fun ri => ri.map (lowBits p.γ₂)
    if normRq z ≥ p.γ₁ - p.β then 0
    else if normR r₀ ≥ p.γ₂ - p.β then 2
    else if normRq (t₀Hat.map fun t => nttInv (multiplyNTT ĉ t)) ≥ p.γ₂ then 3
    else 4

/-- The check of a tag of `signRejectTag`: 0 for `5j`, 2 for `2 + 5i`, the
tag itself for 3 and 4. -/
def coarseTag (t : Nat) : Nat := if t % 5 = 0 then 0 else if t % 5 = 2 then 2 else t

theorem coarseTag_signRejectTag (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) (κ : Nat) :
    coarseTag (signRejectTag p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ) = signRejectTagC p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ := by
  unfold signRejectTag signRejectTagC
  rcases signCommit p Â μ ρ'' κ with ⟨y, w, ct⟩
  dsimp only
  cases sampleInBall p.τ b.ball ct with
  | none => rfl
  | some c =>
    dsimp only
    split
    · simp only [coarseTag, Nat.mul_mod_right, ite_true]
    · split
      · rw [coarseTag, Nat.add_mul_mod_self_left]; rfl
      · split <;> rfl

/-- `signLeakLoop`, with the outcome of each iteration after its `c̃`: the
check that rejected it if one did, 1 (then its hint) if it passes. -/
def signLeakLoopT (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) : (iters κ : Nat) → List Nat
  | 0, _ => []
  | iters + 1, κ =>
    leakBytes (signCommit p Â μ ρ'' κ).2.2 ++
      match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
      | some (_, none) =>
        signRejectTagC p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ :: signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters (κ + p.ℓ)
      | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
      | none => []

/-- The tag of a rejected iteration is never that of one that passes. -/
theorem signRejectTagC_ne_one (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) (κ : Nat) : signRejectTagC p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ ≠ 1 := by
  unfold signRejectTagC
  dsimp only
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split <;> decide

/-- `signLeak`, with `signLeakLoopT` for `signLeakLoop`. -/
def signLeakT (p : Params) (sk μ rnd : List Byte) : List Nat :=
  let (ρ, K, _tr, s₁, s₂, t₀) := skDecode p sk
  leakBytes ρ ++
    match expandA p maxBounds ρ with
    | none => []
    | some Â =>
      signLeakLoopT p maxBounds Â (s₁.map fun s => ntt (toRq s)) (s₂.map fun s => ntt (toRq s))
        (t₀.map fun t => ntt (toRq t)) μ (H (K ++ rnd ++ μ) 64) maxBounds.sign 0

theorem signRejectTag_ne_one (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) (κ : Nat) : signRejectTag p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ ≠ 1 := by
  unfold signRejectTag
  dsimp only
  split
  · decide
  · split
    · omega
    · split
      · omega
      · split <;> decide

/-- `signLeakT` from the contract's `signLeak`, for `iters` iterations: after
each `c̃` (`λ/4` numbers), the end of the list if `SampleInBall` did not
finish, 1 and the hint if the iteration passed, and otherwise its tag, as
`coarseTag` leaves it, and the next iteration. -/
def coarsenLoop (p : Params) : (iters : Nat) → List Nat → List Nat
  | 0, _ => []
  | iters + 1, L =>
    L.take p.ctildeLen ++
      match L.drop p.ctildeLen with
      | [] => []
      | 1 :: h => 1 :: h
      | t :: rest => coarseTag t :: coarsenLoop p iters rest

/-- `coarsenLoop` after the `n` numbers of `ρ`. -/
def coarsen (p : Params) (n : Nat) (L : List Nat) : List Nat :=
  L.take n ++ coarsenLoop p maxBounds.sign (L.drop n)

theorem coarsenLoop_nil (p : Params) : ∀ iters, coarsenLoop p iters [] = []
  | 0 => rfl
  | _ + 1 => by simp only [coarsenLoop, List.take_nil, List.drop_nil, List.nil_append]

/-- `signLeakLoopT` is what `coarsenLoop` leaves of the contract's
`signLeakLoop`. -/
theorem coarsenLoop_signLeakLoop (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) : ∀ iters κ,
    coarsenLoop p iters (signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ) = signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ
  | 0, _ => rfl
  | iters + 1, κ => by
    have ih := coarsenLoop_signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters (κ + p.ℓ)
    have hl : (leakBytes (signCommit p Â μ ρ'' κ).2.2).length = p.ctildeLen := by
      rw [leakBytes, List.length_map]; exact H_length _ _
    unfold signLeakLoop signLeakLoopT
    rw [coarsenLoop, List.take_left' hl, List.drop_left' hl]
    cases signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
    | none => rfl
    | some r =>
      rcases r with ⟨_, _ | _⟩
      · dsimp only
        have h1 := signRejectTag_ne_one p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ
        have hc := coarseTag_signRejectTag p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ
        generalize signRejectTag p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = t at h1 hc ⊢
        rcases t with _ | _ | t
        · rw [← hc, ← ih]; rfl
        · exact absurd rfl h1
        · rw [← hc, ← ih]; rfl
      · rfl

/-- `signLeakT` is what `coarsen` leaves of the contract's `signLeak`, after
the `ρ` of the private key. -/
theorem signLeakT_eq_coarsen (p : Params) (sk μ rnd : List Byte) :
    signLeakT p sk μ rnd = coarsen p (sk.take 32).length (signLeak p sk μ rnd) := by
  unfold signLeakT signLeak coarsen
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [show sk.take 32 = (skDecode p sk).1 from rfl, e]
  dsimp only
  have hl : (leakBytes ρ).length = (sk.take 32).length := by rw [hρ]; exact List.length_map _
  rw [List.take_left' hl, List.drop_left' hl]
  congr 1
  cases expandA p maxBounds ρ with
  | none => exact (coarsenLoop_nil p _).symm
  | some Â => exact (coarsenLoop_signLeakLoop _ _ _ _ _ _ _ _ _ _).symm

/-- Two runs that agree on the contract's `signLeak`, with private keys of the
same length, agree on `signLeakT`. -/
theorem signLeakT_congr (p : Params) {sk sk' μ μ' rnd rnd' : List Byte} (hl : sk.length = sk'.length)
    (h : signLeak p sk μ rnd = signLeak p sk' μ' rnd') : signLeakT p sk μ rnd = signLeakT p sk' μ' rnd' := by
  rw [signLeakT_eq_coarsen, signLeakT_eq_coarsen, h, List.length_take, List.length_take, hl]

theorem leakBytes_inj : ∀ {a b : List Byte}, leakBytes a = leakBytes b → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [leakBytes, List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, leakBytes_inj h.2]
  | [], _ :: _, h => by simp [leakBytes] at h
  | _ :: _, [], h => by simp [leakBytes] at h

theorem leakBytes_length (a : List Byte) : (leakBytes a).length = a.length := List.length_map _

/-- How an iteration ended, as `signLeakLoopT` lists it after its `c̃`. -/
def outTag : Option (List Byte × Option (List Poly × List (Vector Bool n))) → List Nat
  | some (_, none) => [0]
  | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
  | none => []

theorem signCommit_length (p : Params) (Â : List (List Poly)) (μ ρ'' : List Byte) (κ : Nat) :
    (signCommit p Â μ ρ'' κ).2.2.length = p.ctildeLen := H_length _ _

section
variable {p : Params} {b : Bounds}
  {Â₁ Â₂ : List (List Poly)} {s₁ s₁' t₁ s₂ s₂' t₂ : List Poly} {μ₁ μ₂ ρ₁ ρ₂ : List Byte}

/-- Two runs that agree on what an iteration leaks agree on its `c̃`, on
whether it finished, was rejected or passed, and on the hint if it passed;
and, if it was rejected, on what the following iterations leak. -/
theorem leakT_step {n κ : Nat}
    (h : signLeakLoopT p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ (n + 1) κ = signLeakLoopT p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ (n + 1) κ) :
    (signCommit p Â₁ μ₁ ρ₁ κ).2.2 = (signCommit p Â₂ μ₂ ρ₂ κ).2.2 ∧
      ((∃ ct, signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ = some (ct, none)) →
        (∃ ct, signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ = some (ct, none)) ∧
        signLeakLoopT p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ n (κ + p.ℓ) = signLeakLoopT p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ n (κ + p.ℓ)) ∧
      outTag (signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ) = outTag (signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ) := by
  simp only [signLeakLoopT] at h
  have hl : (leakBytes (signCommit p Â₁ μ₁ ρ₁ κ).2.2).length = (leakBytes (signCommit p Â₂ μ₂ ρ₂ κ).2.2).length := by
    rw [leakBytes_length, leakBytes_length, signCommit_length, signCommit_length]
  obtain ⟨hc, hr⟩ := List.append_inj h hl
  refine ⟨leakBytes_inj hc, ?_, ?_⟩
  · rintro ⟨ct, e₁⟩
    rw [e₁] at hr
    dsimp only at hr
    cases e₂ : signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
    | none => rw [e₂] at hr; cases hr
    | some r =>
      obtain ⟨ct', o⟩ := r
      rw [e₂] at hr
      cases o with
      | none => exact ⟨⟨ct', rfl⟩, List.cons.inj hr |>.2⟩
      | some zh => exact absurd (List.cons.inj hr).1 (signRejectTagC_ne_one _ _ _ _ _ _ _ _ _)
  · revert hr
    cases signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ with
    | none =>
      cases signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
      | none => intro; rfl
      | some r => obtain ⟨_, o⟩ := r; cases o <;> intro hr <;> cases hr
    | some r =>
      obtain ⟨_, o⟩ := r
      cases signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
      | none => cases o <;> intro hr <;> cases hr
      | some r' =>
        obtain ⟨_, o'⟩ := r'
        cases o with
        | none =>
          cases o' with
          | none => intro; rfl
          | some _ => intro hr; exact absurd (List.cons.inj hr).1 (signRejectTagC_ne_one _ _ _ _ _ _ _ _ _)
        | some zh =>
          cases o' with
          | none => intro hr; exact absurd (List.cons.inj hr).1.symm (signRejectTagC_ne_one _ _ _ _ _ _ _ _ _)
          | some zh' => intro hr; simp only [outTag]; exact hr

/-- Two runs that agree on what an iteration leaks, and both reject it,
agree on which check rejected it. -/
theorem leakT_tag {n κ : Nat}
    (h : signLeakLoopT p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ (n + 1) κ = signLeakLoopT p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ (n + 1) κ)
    {ct₁ ct₂ : List Byte} (e₁ : signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ = some (ct₁, none))
    (e₂ : signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ = some (ct₂, none)) :
    signRejectTagC p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ = signRejectTagC p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ := by
  simp only [signLeakLoopT] at h
  have hl : (leakBytes (signCommit p Â₁ μ₁ ρ₁ κ).2.2).length = (leakBytes (signCommit p Â₂ μ₂ ρ₂ κ).2.2).length := by
    rw [leakBytes_length, leakBytes_length, signCommit_length, signCommit_length]
  have hr := (List.append_inj h hl).2
  rw [e₁, e₂] at hr
  exact (List.cons.inj hr).1

/-- `leakT_step` for the contract's `signLeakLoop`: two runs that agree on
what an iteration leaks agree on its `c̃`, on
whether it finished, was rejected or passed, and on the hint if it passed;
and, if it was rejected, on what the following iterations leak. -/
theorem leakF_step {n κ : Nat}
    (h : signLeakLoop p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ (n + 1) κ = signLeakLoop p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ (n + 1) κ) :
    (signCommit p Â₁ μ₁ ρ₁ κ).2.2 = (signCommit p Â₂ μ₂ ρ₂ κ).2.2 ∧
      ((∃ ct, signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ = some (ct, none)) →
        (∃ ct, signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ = some (ct, none)) ∧
        signLeakLoop p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ n (κ + p.ℓ) = signLeakLoop p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ n (κ + p.ℓ)) ∧
      outTag (signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ) = outTag (signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ) := by
  simp only [signLeakLoop] at h
  have hl : (leakBytes (signCommit p Â₁ μ₁ ρ₁ κ).2.2).length = (leakBytes (signCommit p Â₂ μ₂ ρ₂ κ).2.2).length := by
    rw [leakBytes_length, leakBytes_length, signCommit_length, signCommit_length]
  obtain ⟨hc, hr⟩ := List.append_inj h hl
  refine ⟨leakBytes_inj hc, ?_, ?_⟩
  · rintro ⟨ct, e₁⟩
    rw [e₁] at hr
    dsimp only at hr
    cases e₂ : signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
    | none => rw [e₂] at hr; cases hr
    | some r =>
      obtain ⟨ct', o⟩ := r
      rw [e₂] at hr
      cases o with
      | none => exact ⟨⟨ct', rfl⟩, List.cons.inj hr |>.2⟩
      | some zh => exact absurd (List.cons.inj hr).1 (signRejectTag_ne_one _ _ _ _ _ _ _ _ _)
  · revert hr
    cases signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ with
    | none =>
      cases signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
      | none => intro; rfl
      | some r => obtain ⟨_, o⟩ := r; cases o <;> intro hr <;> cases hr
    | some r =>
      obtain ⟨_, o⟩ := r
      cases signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ with
      | none => cases o <;> intro hr <;> cases hr
      | some r' =>
        obtain ⟨_, o'⟩ := r'
        cases o with
        | none =>
          cases o' with
          | none => intro; rfl
          | some _ => intro hr; exact absurd (List.cons.inj hr).1 (signRejectTag_ne_one _ _ _ _ _ _ _ _ _)
        | some zh =>
          cases o' with
          | none => intro hr; exact absurd (List.cons.inj hr).1.symm (signRejectTag_ne_one _ _ _ _ _ _ _ _ _)
          | some zh' => intro hr; simp only [outTag]; exact hr

/-- `leakT_tag` for the contract's `signLeakLoop`: two runs that agree on
what an iteration leaks, and both reject it,
agree on which check rejected it, and at which polynomial. -/
theorem leakF_tag {n κ : Nat}
    (h : signLeakLoop p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ (n + 1) κ = signLeakLoop p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ (n + 1) κ)
    {ct₁ ct₂ : List Byte} (e₁ : signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ = some (ct₁, none))
    (e₂ : signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ = some (ct₂, none)) :
    signRejectTag p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ = signRejectTag p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ := by
  simp only [signLeakLoop] at h
  have hl : (leakBytes (signCommit p Â₁ μ₁ ρ₁ κ).2.2).length = (leakBytes (signCommit p Â₂ μ₂ ρ₂ κ).2.2).length := by
    rw [leakBytes_length, leakBytes_length, signCommit_length, signCommit_length]
  have hr := (List.append_inj h hl).2
  rw [e₁, e₂] at hr
  exact (List.cons.inj hr).1

end

theorem signLeakLoopT_succ (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) (n κ : Nat) :
    signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (n + 1) κ =
      leakBytes (signCommit p Â μ ρ'' κ).2.2 ++
        match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
        | some (_, none) =>
          signRejectTagC p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ :: signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n (κ + p.ℓ)
        | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
        | none => [] := rfl

/-! ## Contracts that leak `signLeakT` -/

/-- `f` with `φ` applied to its result. -/
def Curry.post {α β : Type} (φ : α → β) : (ws : List ArgWord) → Curry ws α → Curry ws β
  | [], f => φ f
  | _ :: ws, f => fun a => Curry.post φ ws (f a)

theorem Curry.apply_post {α β : Type} (φ : α → β) :
    ∀ (ws : List ArgWord) (f : Curry ws α) (v : List (BitVec 64)), Curry.apply ws (Curry.post φ ws f) v = φ (Curry.apply ws f v)
  | [], _, _ => rfl
  | _ :: ws, _, [] => Curry.apply_post φ ws _ []
  | _ :: ws, _, _ :: v => Curry.apply_post φ ws _ v

/-- Two runs that agree on what a contract built with `Sig.contract` takes as
public with the leakage `f` agree on it with the leakage `Curry.post φ f`. -/
theorem contract_pub_post {M : ISA} {sig : Sig} {A : Abi M} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {st : Nat} {f : Curry (sig.words A.ptrBits) (Mem → List Nat)}
    (φ : List Nat → List Nat) {s₁ s₂ : M.State} (h : (sig.contract A pre post wa st (some f)).pub s₁ s₂) :
    (sig.contract A pre post wa st (some (Curry.post (fun F m => φ (F m)) _ f))).pub s₁ s₂ := by
  revert h
  unfold Sig.contract
  dsimp only
  split
  · exact id
  · rintro ⟨⟨a, e⟩, c⟩
    exact ⟨⟨a, by rw [Curry.apply_post, Curry.apply_post, e]⟩, c⟩

/-- Two runs that agree on `signContract`'s public data agree on that of
the same contract with `signLeakT` for `signLeak`, against which the
implementations that run each check on all its polynomials are proven. -/
theorem signContract_pubT {M : ISA} {A : Abi M} {stack : Nat} {p : Params} {s₁ s₂ : M.State}
    (h : (signContract p A stack).pub s₁ s₂) :
    ((signSig p).contract A
      (post := fun sk mu rnd sig _scratch m m' r =>
        Outcome (fun b => signMu p b (VG.Spec.Sha3.bytesAt m sk p.skLen) (VG.Spec.Sha3.bytesAt m mu 64)
          (VG.Spec.Sha3.bytesAt m rnd 32)) r (VG.Spec.Sha3.bytesAt m' sig p.sigLen))
      (writeArgs := true)
      (stack := stack)
      (leak := some fun sk mu rnd _sig _scratch m =>
        signLeakT p (VG.Spec.Sha3.bytesAt m sk p.skLen) (VG.Spec.Sha3.bytesAt m mu 64)
          (VG.Spec.Sha3.bytesAt m rnd 32))).pub s₁ s₂ := by
  have e := contract_pub_post (coarsen p (min 32 p.skLen)) h
  have hg : @Eq (Curry ((signSig p).words A.ptrBits) (Mem → List Nat))
      (fun sk mu rnd _sig _scratch m =>
        signLeakT p (VG.Spec.Sha3.bytesAt m sk p.skLen) (VG.Spec.Sha3.bytesAt m mu 64)
          (VG.Spec.Sha3.bytesAt m rnd 32))
      (Curry.post (fun (F : Mem → List Nat) m => coarsen p (min 32 p.skLen) (F m)) ((signSig p).words A.ptrBits)
        (fun sk mu rnd _sig _scratch m =>
          signLeak p (VG.Spec.Sha3.bytesAt m sk p.skLen) (VG.Spec.Sha3.bytesAt m mu 64)
            (VG.Spec.Sha3.bytesAt m rnd 32))) := by
    funext sk mu rnd sig scratch m
    rw [signLeakT_eq_coarsen, List.length_take]
    simp only [VG.Spec.Sha3.bytesAt, List.length_map, List.length_range]
    rfl
  rw [hg]
  exact e

end VG.Proof.MlDsa.Sign
