import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sign.Bounds`. -/
section

/-!
# ML-DSA: the samplers are monotone in their bounds

The XOFs' output for a larger length extends the output for a smaller one
(`H_take`, `G_take`), so `RejNTTPoly`, `SampleInBall` and `ExpandA` that
finish within a bound give the same result within any larger one
(`rejNTTPoly_mono`, `sampleInBall_mono`, `expandA_mono`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa
open VG.Spec.Sha3 (squeeze shake128 shake256 keccak sponge)
open VG.Proof.Sha3 (length_squeeze squeeze_getElem)

theorem ifp {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-! ## The XOFs -/

/-- The first `d` bytes of a longer output. -/
theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : Spec.Sha3.State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [length_squeeze hr hr'] at h₂
  rw [List.getElem_take, squeeze_getElem hr hr' _ h₂, squeeze_getElem hr hr' _ (by omega)]

theorem H_length (s : List Byte) (d : Nat) : (H s d).length = d := length_squeeze (by decide) (by decide) _ _

theorem G_length (s : List Byte) (d : Nat) : (G s d).length = d := length_squeeze (by decide) (by decide) _ _

theorem H_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (H s d').take d = H s d :=
  VG.Proof.MlDsa.Sign.squeeze_take (by decide) (by decide) _ h

theorem G_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (G s d').take d = G s d :=
  VG.Proof.MlDsa.Sign.squeeze_take (by decide) (by decide) _ h

theorem H_extend (s : List Byte) {d d' : Nat} (h : d ≤ d') : H s d' = H s d ++ (H s d').drop d := by
  rw [← VG.Proof.MlDsa.Sign.H_take s h, List.take_append_drop]

theorem G_extend (s : List Byte) {d d' : Nat} (h : d ≤ d') : G s d' = G s d ++ (G s d').drop d := by
  rw [← VG.Proof.MlDsa.Sign.G_take s h, List.take_append_drop]

/-! ## `RejNTTPoly` -/

theorem rejNTTLoop_append : ∀ (a : List Zq) (out more : List Byte) (x : List Zq),
    rejNTTLoop a out = some x → rejNTTLoop a (out ++ more) = some x
  | a, s₀ :: s₁ :: s₂ :: out, more, x, h => by
    simp only [rejNTTLoop, List.cons_append] at h ⊢
    split at h
    · rw [VG.Proof.MlDsa.Sign.ifp ‹_›]; exact h
    · rw [VG.Proof.MlDsa.Sign.ifn ‹_›]; exact VG.Proof.MlDsa.Sign.rejNTTLoop_append _ out more x h
  | a, [], more, x, h => by
    have ha : a.length ≥ n ∧ a = x := by simpa [rejNTTLoop] using h
    obtain ⟨hl, rfl⟩ := ha
    match more with
    | s₀ :: s₁ :: s₂ :: _ => simp [rejNTTLoop, hl]
    | [] => simp [rejNTTLoop, hl]
    | [_] => simp [rejNTTLoop, hl]
    | [_, _] => simp [rejNTTLoop, hl]
  | a, [s₀], more, x, h => by
    have ha : a.length ≥ n ∧ a = x := by simpa [rejNTTLoop] using h
    obtain ⟨hl, rfl⟩ := ha
    match more with
    | s₁ :: s₂ :: _ => simp [rejNTTLoop, hl]
    | [] => simp [rejNTTLoop, hl]
    | [_] => simp [rejNTTLoop, hl]
  | a, [s₀, s₁], more, x, h => by
    have ha : a.length ≥ n ∧ a = x := by simpa [rejNTTLoop] using h
    obtain ⟨hl, rfl⟩ := ha
    match more with
    | s₂ :: _ => simp [rejNTTLoop, hl]
    | [] => simp [rejNTTLoop, hl]

theorem rejNTTPoly_mono {b b' : Nat} (hb : b ≤ b') {ρ : List Byte} {x : Poly}
    (h : rejNTTPoly b ρ = some x) : rejNTTPoly b' ρ = some x := by
  unfold rejNTTPoly at h ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [VG.Proof.MlDsa.Sign.G_extend ρ hb, VG.Proof.MlDsa.Sign.rejNTTLoop_append _ _ _ _ ha]
  rfl

/-! ## `SampleInBall` -/

theorem ballLoop_append (τ : Nat) (hb : Array Bool) : ∀ (c : IPoly) (i : Nat) (out more : List Byte) (x : IPoly),
    ballLoop τ hb c i out = some x → ballLoop τ hb c i (out ++ more) = some x
  | c, i, [], more, x, h => by
    have hc : i ≥ n ∧ c = x := by simpa [ballLoop] using h
    obtain ⟨hi, rfl⟩ := hc
    cases more with
    | nil => simp [ballLoop, hi]
    | cons j more => simp [ballLoop, hi]
  | c, i, j :: out, more, x, h => by
    simp only [ballLoop, List.cons_append] at h ⊢
    split at h
    · rw [VG.Proof.MlDsa.Sign.ifp ‹_›]; exact h
    · rw [VG.Proof.MlDsa.Sign.ifn ‹_›]
      split at h
      · rw [VG.Proof.MlDsa.Sign.ifp ‹_›]; exact VG.Proof.MlDsa.Sign.ballLoop_append τ hb c i out more x h
      · rw [VG.Proof.MlDsa.Sign.ifn ‹_›]; exact VG.Proof.MlDsa.Sign.ballLoop_append τ hb _ _ out more x h

theorem sampleInBall_mono {τ b b' : Nat} (hb : b ≤ b') {ρ : List Byte} {x : IPoly}
    (h : sampleInBall τ b ρ = some x) : sampleInBall τ b' ρ = some x := by
  unfold sampleInBall at h ⊢
  have hl : ¬ (H ρ b).length < 8 := fun hl => by rw [VG.Proof.MlDsa.Sign.ifp hl] at h; cases h
  rw [VG.Proof.MlDsa.Sign.ifn hl] at h
  have hl' : ¬ (H ρ b').length < 8 := by rw [VG.Proof.MlDsa.Sign.H_length] at hl ⊢; omega
  rw [VG.Proof.MlDsa.Sign.ifn hl', VG.Proof.MlDsa.Sign.H_extend ρ hb, List.take_append_of_le_length (by omega),
    List.drop_append_of_le_length (by omega)]
  exact VG.Proof.MlDsa.Sign.ballLoop_append τ _ _ _ _ _ _ h

/-! ## `ExpandA` -/

theorem mapM_some_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → (∀ x ∈ l, ∀ y, f x = some y → g x = some y) →
      l.mapM g = some ys
  | [], ys, h, _ => by simpa using h
  | x :: l, ys, h, hfg => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys', hys, h⟩ := Option.bind_eq_some_iff.mp h
    have hl := VG.Proof.MlDsa.Sign.mapM_some_congr hys fun x hx => hfg x (List.mem_cons_of_mem _ hx)
    simp only [hfg x (List.mem_cons_self ..) y hy, hl, Option.bind_eq_bind, Option.bind_some]
    exact h

theorem expandA_mono {p : Params} {b b' : Bounds} (hb : b.rejNTT ≤ b'.rejNTT) {ρ : List Byte}
    {A : List (List Poly)} (h : expandA p b ρ = some A) : expandA p b' ρ = some A := by
  unfold expandA at h ⊢
  exact VG.Proof.MlDsa.Sign.mapM_some_congr h fun _ _ _ hr => VG.Proof.MlDsa.Sign.mapM_some_congr hr fun _ _ _ hy => VG.Proof.MlDsa.Sign.rejNTTPoly_mono hb hy

theorem minBounds_le_max : minBounds.rejNTT ≤ maxBounds.rejNTT ∧ minBounds.ball ≤ maxBounds.ball ∧
    minBounds.sign ≤ maxBounds.sign := by decide

end VG.Proof.MlDsa.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sign.Loop`. -/
section

/-!
# ML-DSA: the signing loop

An iteration of the signing loop (`signIteration`) is its commitment,
`SampleInBall` of its `c̃`, and the validity checks (`iterOut`), all computed
from `c` (`signIteration_eq`): so it depends on the bounds only through
`SampleInBall`, and a larger bound gives the same result once a smaller one
finishes (`signIteration_mono`, `signIteration_min`). The loop (`signLoop`)
returns the first iteration that passes after iterations that were rejected
(`signLoop_pass`), and nothing if all of them were rejected
(`signLoop_exhaust`); within smaller bounds, it returns nothing if the larger
bounds reject every iteration before one whose `SampleInBall` does not finish
within the smaller ones (`signLoop_min_none`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

section
variable (p : Params) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly) (μ ρ'' : List Byte)

/-- What an iteration computes once `c` is sampled: `(z, h)` if the
validity checks pass (lines 17–30 of Algorithm 7). -/
def iterOut (y : List IPoly) (w : List Poly) (c : IPoly) : Option (List Poly × List (Vector Bool n)) :=
  let ĉ := ntt (toRq c)
  let cs₁ := ŝ₁.map fun s => nttInv (multiplyNTT ĉ s)
  let cs₂ := ŝ₂.map fun s => nttInv (multiplyNTT ĉ s)
  let z := addVec (y.map toRq) cs₁
  let r₀ := (subVec w cs₂).map fun ri => ri.map (lowBits p.γ₂)
  let ct₀ := t₀Hat.map fun t => nttInv (multiplyNTT ĉ t)
  let h := List.zipWith (fun u v => Vector.zipWith (makeHint p.γ₂) u v)
    (ct₀.map neg) (addVec (subVec w cs₂) ct₀)
  let ones := (h.map fun hi => (hi.toList.filter id).length).sum
  if normRq z ≥ p.γ₁ - p.β ∨ normR r₀ ≥ p.γ₂ - p.β ∨ normRq ct₀ ≥ p.γ₂ ∨ ones > p.ω then none
  else some (z, h)

/-- An iteration: its `c̃` and, if `SampleInBall` finishes, the outcome of its checks. -/
theorem signIteration_eq (b : Bounds) (κ : Nat) :
    signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ =
      (sampleInBall p.τ b.ball (signCommit p Â μ ρ'' κ).2.2).map fun c =>
        ((signCommit p Â μ ρ'' κ).2.2,
          VG.Proof.MlDsa.Sign.iterOut p ŝ₁ ŝ₂ t₀Hat (signCommit p Â μ ρ'' κ).1 (signCommit p Â μ ρ'' κ).2.1 c) := by
  unfold signIteration VG.Proof.MlDsa.Sign.iterOut
  rcases signCommit p Â μ ρ'' κ with ⟨y, w, ct⟩
  dsimp only
  cases sampleInBall p.τ b.ball ct with
  | none => rfl
  | some c =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    by_cases h1 : normRq (addVec (y.map toRq) (ŝ₁.map fun s => nttInv (multiplyNTT (ntt (toRq c)) s))) ≥ p.γ₁ - p.β ∨
      normR ((subVec w (ŝ₂.map fun s => nttInv (multiplyNTT (ntt (toRq c)) s))).map fun ri => ri.map (lowBits p.γ₂)) ≥
        p.γ₂ - p.β
    · rw [VG.Proof.MlDsa.Sign.ifp h1, VG.Proof.MlDsa.Sign.ifp (h1.elim Or.inl fun h => Or.inr (Or.inl h))]; rfl
    · rw [VG.Proof.MlDsa.Sign.ifn h1]
      split
      · rename_i h2; rw [VG.Proof.MlDsa.Sign.ifp (by omega)]; rfl
      · rename_i h2; rw [VG.Proof.MlDsa.Sign.ifn (by omega)]; rfl

theorem signIteration_mono {b b' : Bounds} (hb : b.ball ≤ b'.ball) {κ : Nat}
    {r : List Byte × Option (List Poly × List (Vector Bool n))}
    (h : signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = some r) : signIteration p b' Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = some r := by
  rw [VG.Proof.MlDsa.Sign.signIteration_eq] at h ⊢
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [VG.Proof.MlDsa.Sign.sampleInBall_mono hb hc]; rfl

/-- Within a smaller bound, an iteration either does not finish or has the same outcome. -/
theorem signIteration_min {b b' : Bounds} (hb : b.ball ≤ b'.ball) {κ : Nat}
    {r : List Byte × Option (List Poly × List (Vector Bool n))}
    (h : signIteration p b' Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = some r) :
    signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = none ∨ signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ = some r := by
  cases e : signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
  | none => exact .inl rfl
  | some r' => rw [VG.Proof.MlDsa.Sign.signIteration_mono p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' hb e] at h; exact .inr (congrArg some (Option.some.inj h))

/-! ## The loop -/

theorem signLoop_succ (b : Bounds) (n κ : Nat) :
    signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (n + 1) κ =
      match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
      | none => none
      | some (ct, some (z, h)) => some (ct, z, h)
      | some (_, none) => signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n (κ + p.ℓ) := by
  simp only [signLoop, Option.bind_eq_bind]
  cases signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
  | none => rfl
  | some r =>
    obtain ⟨ct, o⟩ := r
    cases o with
    | none => rfl
    | some zh => rfl

/-- The `i` iterations from the counter `κ` are rejected within the bounds `b`. -/
def Rej (b : Bounds) (κ i : Nat) : Prop :=
  ∀ j < i, ∃ ct, signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (κ + p.ℓ * j) = some (ct, none)

theorem Rej.succ {b : Bounds} {κ i : Nat} (h : VG.Proof.MlDsa.Sign.Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b κ i) {ct : List Byte}
    (hi : signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (κ + p.ℓ * i) = some (ct, none)) :
    VG.Proof.MlDsa.Sign.Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b κ (i + 1) := fun j hj => by
  rcases (by omega : j < i ∨ j = i) with hj | rfl
  exacts [h j hj, ⟨ct, hi⟩]

theorem Rej.tail {b : Bounds} {κ i : Nat} (h : VG.Proof.MlDsa.Sign.Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b κ (i + 1)) :
    VG.Proof.MlDsa.Sign.Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b (κ + p.ℓ) i := fun j hj => by
  obtain ⟨ct, hc⟩ := h (j + 1) (by omega)
  exact ⟨ct, by rw [show κ + p.ℓ + p.ℓ * j = κ + p.ℓ * (j + 1) by rw [Nat.mul_succ]; omega]; exact hc⟩

/-- Rejected iterations are skipped. -/
theorem signLoop_rej {b : Bounds} : ∀ {i κ n : Nat}, VG.Proof.MlDsa.Sign.Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b κ i → i ≤ n →
    signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n κ = signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (n - i) (κ + p.ℓ * i)
  | 0, κ, n, _, _ => by simp
  | i + 1, κ, n + 1, h, hi => by
    obtain ⟨ct, hc⟩ := h 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at hc
    rw [VG.Proof.MlDsa.Sign.signLoop_succ, hc]
    dsimp only
    rw [VG.Proof.MlDsa.Sign.signLoop_rej h.tail (by omega), show n + 1 - (i + 1) = n - i by omega,
      show κ + p.ℓ + p.ℓ * i = κ + p.ℓ * (i + 1) by rw [Nat.mul_succ]; omega]
  | _ + 1, _, 0, _, hi => absurd hi (by omega)

theorem signLoop_pass {b : Bounds} {i N : Nat} (h : VG.Proof.MlDsa.Sign.Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b 0 i) (hi : i < N)
    {ct : List Byte} {z : List Poly} {hh : List (Vector Bool n)}
    (hp : signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (p.ℓ * i) = some (ct, some (z, hh))) :
    signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' N 0 = some (ct, z, hh) := by
  rw [VG.Proof.MlDsa.Sign.signLoop_rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' h (by omega), Nat.zero_add,
    show N - i = (N - i - 1) + 1 by omega, VG.Proof.MlDsa.Sign.signLoop_succ, hp]

theorem signLoop_exhaust {b : Bounds} {n : Nat} (h : VG.Proof.MlDsa.Sign.Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b 0 n) :
    signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n 0 = none := by
  rw [VG.Proof.MlDsa.Sign.signLoop_rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' h (Nat.le_refl _), Nat.sub_self]; rfl

/-- Within smaller bounds `b`, the loop returns nothing if the larger bounds
`b'` reject the `i` iterations from `κ`, and the loop ends within them or at
an iteration whose `SampleInBall` does not finish within `b`. -/
theorem signLoop_min_none {b b' : Bounds} (hb : b.ball ≤ b'.ball) :
    ∀ {i κ n : Nat}, VG.Proof.MlDsa.Sign.Rej p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' b' κ i →
      (n ≤ i ∨ signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (κ + p.ℓ * i) = none) →
      signLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n κ = none
  | _, _, 0, _, _ => rfl
  | 0, κ, n + 1, _, hs => by
    rcases hs with hs | hs
    · omega
    · rw [Nat.mul_zero, Nat.add_zero] at hs; rw [VG.Proof.MlDsa.Sign.signLoop_succ, hs]
  | i + 1, κ, n + 1, h, hs => by
    obtain ⟨ct, hc⟩ := h 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at hc
    rw [VG.Proof.MlDsa.Sign.signLoop_succ]
    rcases VG.Proof.MlDsa.Sign.signIteration_min p Â ŝ₁ ŝ₂ t₀Hat μ ρ'' hb hc with e | e
    · rw [e]
    · rw [e]
      dsimp only
      refine VG.Proof.MlDsa.Sign.signLoop_min_none hb h.tail ?_
      rcases hs with hs | hs
      · exact .inl (by omega)
      · exact .inr (by rw [show κ + p.ℓ + p.ℓ * i = κ + p.ℓ * (i + 1) by rw [Nat.mul_succ]; omega]; exact hs)

end

/-! ## `Sign_internal` -/

/-- Algorithm 7 with `μ` given, as the matrix and the loop. -/
theorem signMu_eq (p : Params) (b : Bounds) (sk μ rnd : List Byte) :
    signMu p b sk μ rnd =
      (expandA p b (skDecode p sk).1).bind fun Â =>
        (signLoop p b Â ((skDecode p sk).2.2.2.1.map fun s => ntt (toRq s))
          ((skDecode p sk).2.2.2.2.1.map fun s => ntt (toRq s)) ((skDecode p sk).2.2.2.2.2.map fun t => ntt (toRq t))
          μ (H ((skDecode p sk).2.1 ++ rnd ++ μ) 64) b.sign 0).map fun r =>
          sigEncode p r.1 (r.2.1.map fun zi => zi.map fun c => modPm c.val q) r.2.2 := by
  unfold signMu
  rcases skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  dsimp only
  cases expandA p b ρ with
  | none => rfl
  | some Â =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases signLoop p b Â (s₁.map fun s => ntt (toRq s)) (s₂.map fun s => ntt (toRq s)) (t₀.map fun t => ntt (toRq t))
      μ (H (K ++ rnd ++ μ) 64) b.sign 0 with
    | none => rfl
    | some r => rfl

end VG.Proof.MlDsa.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sign.Iter`. -/
section

/-!
# ML-DSA: signing polynomial by polynomial

An implementation computes the vectors of signing one polynomial at a time, in
buffers of their own: this file states the algorithm's lists as `List.range n`
mapped by a function of the index, for the matrix, the private key, and each
value of an iteration of the signing loop (`yF`, `wF`, `zF`, `hF`, …), so that
`signCommit` (`signCommit_eq`), the validity checks (`iterOut_eq`, with each
norm checked polynomial by polynomial, `passF`) and `signIteration`
(`signIteration_eqF`) read as what the implementation computes. The norm of
`r₀`, a vector of `R` of `LowBits`, is that of its image in `R_q`
(`normR_lowBits`), which the implementation stores.
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (foldl_max_lt normZq_lt mem_gamma2s q_eq)

/-! ## Lists by index -/

theorem zipWith_range {α β γ : Type} (f : α → β → γ) (a : Nat → α) (b : Nat → β) (m : Nat) :
    List.zipWith f ((List.range m).map a) ((List.range m).map b) = (List.range m).map fun i => f (a i) (b i) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

theorem getD_range {α : Type} (f : Nat → α) {m i : Nat} (hi : i < m) (d : α) : ((List.range m).map f).getD i d = f i := by
  simp [hi]

/-! ## Norms -/

theorem normRq_lt_iff (v : List Poly) {B : Nat} (hB : 0 < B) : normRq v < B ↔ ∀ f ∈ v, normRq [f] < B := by
  simp only [normRq, foldl_max_lt, List.mem_flatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  constructor
  · rintro ⟨_, h⟩ f hf
    exact ⟨hB, fun x hx => h x ⟨f, hf, hx⟩⟩
  · intro h
    exact ⟨hB, fun x ⟨f, hf, hx⟩ => (h f hf).2 x hx⟩

theorem normR_lt_iff (v : List IPoly) {B : Nat} (hB : 0 < B) : normR v < B ↔ ∀ f ∈ v, normR [f] < B := by
  simp only [normR, foldl_max_lt, List.mem_flatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  constructor
  · rintro ⟨_, h⟩ f hf
    exact ⟨hB, fun x hx => h x ⟨f, hf, hx⟩⟩
  · intro h
    exact ⟨hB, fun x ⟨f, hf, hx⟩ => (h f hf).2 x hx⟩

theorem normRq_range_lt {m : Nat} (f : Nat → Poly) {B : Nat} (hB : 0 < B) :
    normRq ((List.range m).map f) < B ↔ ∀ i < m, normRq [f i] < B := by
  rw [VG.Proof.MlDsa.Sign.normRq_lt_iff _ hB]
  simp

/-- `‖x mod q‖∞ = |x|` for `|x| ≤ (q - 1)/2`. -/
theorem modPm_ofInt {x : Int} (h₁ : -((q - 1) / 2 : Nat) ≤ x) (h₂ : x ≤ ((q - 1) / 2 : Nat)) :
    modPm (ofInt x).val q = x := by
  unfold modPm
  dsimp only
  split <;> (rename_i hc; simp only [ofInt, Fin.val_ofNat, q_eq] at *; omega)

theorem normZq_ofInt {x : Int} (h₁ : -((q - 1) / 2 : Nat) ≤ x) (h₂ : x ≤ ((q - 1) / 2 : Nat)) :
    normZq (ofInt x) = x.natAbs := by
  rw [normZq, VG.Proof.MlDsa.Sign.modPm_ofInt h₁ h₂]

/-- `LowBits(r)` lies in `[-γ₂, γ₂]`. -/
theorem lowBits_range {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    -(γ₂ : Int) ≤ lowBits γ₂ r ∧ lowBits γ₂ r ≤ γ₂ := by
  have hr := r.isLt
  rcases mem_gamma2s h with rfl | rfl <;>
  · simp only [lowBits, decompose, modPm, q_eq] at *
    split <;> split <;> simp only <;> omega

/-- `HighBits(r)` is at most `(q - 1)/(2γ₂) - 1`. -/
theorem highBits_le {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) : (highBits γ₂ r).toNat ≤ (q - 1) / (2 * γ₂) - 1 := by
  rw [VG.Proof.MlDsa.Round.highBits_eq h, Int.toNat_natCast]
  have : 0 < VG.Proof.MlDsa.Round.hbM γ₂ := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have := Nat.mod_lt (VG.Proof.MlDsa.Round.hbF γ₂ r.val) this
  simp only [VG.Proof.MlDsa.Round.hbM] at *
  omega

/-- The norm of a polynomial of `LowBits`, as the implementation stores it in `R_q`. -/
theorem normR_lowBits {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (w : Poly) :
    normR [w.map (lowBits γ₂)] = normRq [w.map fun c => ofInt (lowBits γ₂ c)] := by
  have hq : γ₂ ≤ (q - 1) / 2 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  simp only [normR, normRq, List.flatMap_cons, List.flatMap_nil, List.append_nil, Vector.toList_map, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  have := VG.Proof.MlDsa.Sign.lowBits_range h c
  simp only [Function.comp]
  rw [VG.Proof.MlDsa.Sign.normZq_ofInt (by omega) (by omega)]

/-! ## The iteration, polynomial by polynomial -/

section
variable (p : Params) (A : Nat → Nat → Poly) (S1 S2 T0 : Nat → Poly) (μ ρ'' : List Byte) (κ : Nat)

/-- The matrix of the entries `A i j`. -/
def amat : List (List Poly) := (List.range p.k).map fun i => (List.range p.ℓ).map (A i)

/-- `y[r]` of `ExpandMask(ρ″, κ)`. -/
def yF (r : Nat) : IPoly :=
  bitUnpack (H (ρ'' ++ integerToBytes (κ + r) 2) (32 * (1 + bitlen (p.γ₁ - 1)))) (p.γ₁ - 1) p.γ₁

/-- `NTT(y[r])`. -/
def yhF (r : Nat) : Poly := ntt (toRq (VG.Proof.MlDsa.Sign.yF p ρ'' κ r))

/-- `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])`. -/
def wF (i : Nat) : Poly := nttInv (((List.range p.ℓ).map fun j => multiplyNTT (A i j) (VG.Proof.MlDsa.Sign.yhF p ρ'' κ j)).foldl add zero)

/-- `w₁[i] = HighBits(w[i])`. -/
def w1F (i : Nat) : Vector Nat n := (VG.Proof.MlDsa.Sign.wF p A ρ'' κ i).map fun c => (highBits p.γ₂ c).toNat

/-- `c̃ = H(μ ‖ w1Encode(w₁), λ/4)`. -/
def ctF : List Byte := H (μ ++ w1Encode p ((List.range p.k).map (VG.Proof.MlDsa.Sign.w1F p A ρ'' κ))) p.ctildeLen

theorem signCommit_eq : signCommit p (VG.Proof.MlDsa.Sign.amat p A) μ ρ'' κ =
    ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.yF p ρ'' κ), (List.range p.k).map (VG.Proof.MlDsa.Sign.wF p A ρ'' κ), VG.Proof.MlDsa.Sign.ctF p A μ ρ'' κ) := by
  have hy : expandMask p ρ'' κ = (List.range p.ℓ).map (VG.Proof.MlDsa.Sign.yF p ρ'' κ) := rfl
  have hw : (matrixVectorNTT (VG.Proof.MlDsa.Sign.amat p A) ((expandMask p ρ'' κ).map fun yi => ntt (toRq yi))).map nttInv =
      (List.range p.k).map (VG.Proof.MlDsa.Sign.wF p A ρ'' κ) := by
    rw [hy, List.map_map]
    simp only [matrixVectorNTT, VG.Proof.MlDsa.Sign.amat, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, VG.Proof.MlDsa.Sign.wF]
    congr 2
    exact VG.Proof.MlDsa.Sign.zipWith_range multiplyNTT (A i) (fun j => ntt (toRq (VG.Proof.MlDsa.Sign.yF p ρ'' κ j))) p.ℓ
  simp only [signCommit]
  rw [hw, hy]
  simp only [List.map_map]
  rfl

variable (c : IPoly)

/-- `ĉ = NTT(c)`. -/
def chF : Poly := ntt (toRq c)

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])`. -/
def zF (r : Nat) : Poly := add (toRq (VG.Proof.MlDsa.Sign.yF p ρ'' κ r)) (nttInv (multiplyNTT (VG.Proof.MlDsa.Sign.chF c) (S1 r)))

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])`. -/
def w'F (i : Nat) : Poly := sub (VG.Proof.MlDsa.Sign.wF p A ρ'' κ i) (nttInv (multiplyNTT (VG.Proof.MlDsa.Sign.chF c) (S2 i)))

/-- `r₀[i] = LowBits(w[i] - cs₂[i])`, in `R_q`. -/
def r0F (i : Nat) : Poly := (VG.Proof.MlDsa.Sign.w'F p A S2 ρ'' κ c i).map fun x => ofInt (lowBits p.γ₂ x)

/-- `ct₀[i] = NTT⁻¹(ĉ t̂₀[i])`. -/
def ct0F (i : Nat) : Poly := nttInv (multiplyNTT (VG.Proof.MlDsa.Sign.chF c) (T0 i))

/-- `w[i] - cs₂[i] + ct₀[i]`. -/
def w''F (i : Nat) : Poly := add (VG.Proof.MlDsa.Sign.w'F p A S2 ρ'' κ c i) (VG.Proof.MlDsa.Sign.ct0F T0 c i)

/-- `h[i] = MakeHint(-ct₀[i], w[i] - cs₂[i] + ct₀[i])`. -/
def hF (i : Nat) : Vector Bool n := Vector.zipWith (makeHint p.γ₂) (neg (VG.Proof.MlDsa.Sign.ct0F T0 c i)) (VG.Proof.MlDsa.Sign.w''F p A S2 T0 ρ'' κ c i)

/-- The validity checks of the iteration, polynomial by polynomial. -/
def passF : Prop :=
  (∀ r < p.ℓ, normRq [VG.Proof.MlDsa.Sign.zF p S1 ρ'' κ c r] < p.γ₁ - p.β) ∧ (∀ i < p.k, normRq [VG.Proof.MlDsa.Sign.r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β) ∧
    (∀ i < p.k, normRq [VG.Proof.MlDsa.Sign.ct0F T0 c i] < p.γ₂) ∧ ((List.range p.k).map fun i => hintOnes [VG.Proof.MlDsa.Sign.hF p A S2 T0 ρ'' κ c i]).sum ≤ p.ω

instance : Decidable (VG.Proof.MlDsa.Sign.passF p A S1 S2 T0 ρ'' κ c) := by unfold VG.Proof.MlDsa.Sign.passF; infer_instance

/-- What the parameter sets have that the checks need. -/
structure ParamsOk (p : Params) : Prop where
  pos₁ : 0 < p.γ₁ - p.β
  pos₂ : 0 < p.γ₂ - p.β
  γ₂ : p.γ₂ ∈ gamma2s

theorem hintOnes_single (h : Vector Bool n) : hintOnes [h] = (h.toList.filter id).length := by
  simp [hintOnes]

theorem iterOut_eq (hp : VG.Proof.MlDsa.Sign.ParamsOk p) :
    VG.Proof.MlDsa.Sign.iterOut p ((List.range p.ℓ).map S1) ((List.range p.k).map S2) ((List.range p.k).map T0)
      ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.yF p ρ'' κ)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.wF p A ρ'' κ)) c =
      if VG.Proof.MlDsa.Sign.passF p A S1 S2 T0 ρ'' κ c then
        some ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.zF p S1 ρ'' κ c), (List.range p.k).map (VG.Proof.MlDsa.Sign.hF p A S2 T0 ρ'' κ c))
      else none := by
  have hγ₂ : 0 < p.γ₂ := by have := hp.pos₂; omega
  simp only [VG.Proof.MlDsa.Sign.iterOut, List.map_map]
  have ez : addVec ((List.range p.ℓ).map (toRq ∘ VG.Proof.MlDsa.Sign.yF p ρ'' κ))
      ((List.range p.ℓ).map ((fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ S1)) =
      (List.range p.ℓ).map (VG.Proof.MlDsa.Sign.zF p S1 ρ'' κ c) := VG.Proof.MlDsa.Sign.zipWith_range add _ _ _
  have ew' : subVec ((List.range p.k).map (VG.Proof.MlDsa.Sign.wF p A ρ'' κ))
      ((List.range p.k).map ((fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ S2)) =
      (List.range p.k).map (VG.Proof.MlDsa.Sign.w'F p A S2 ρ'' κ c) := VG.Proof.MlDsa.Sign.zipWith_range sub _ _ _
  have ect : (List.range p.k).map ((fun t => nttInv (multiplyNTT (ntt (toRq c)) t)) ∘ T0) =
      (List.range p.k).map (VG.Proof.MlDsa.Sign.ct0F T0 c) := rfl
  have eh : List.zipWith (fun u v => Vector.zipWith (makeHint p.γ₂) u v)
      ((List.range p.k).map (neg ∘ (fun s => nttInv (multiplyNTT (ntt (toRq c)) s)) ∘ T0))
      (addVec ((List.range p.k).map (VG.Proof.MlDsa.Sign.w'F p A S2 ρ'' κ c)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.ct0F T0 c))) =
      (List.range p.k).map (VG.Proof.MlDsa.Sign.hF p A S2 T0 ρ'' κ c) := by
    rw [addVec, VG.Proof.MlDsa.Sign.zipWith_range add, VG.Proof.MlDsa.Sign.zipWith_range]; rfl
  rw [ez, ew', ect, List.map_map, eh]
  have c1 : normRq ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.zF p S1 ρ'' κ c)) ≥ p.γ₁ - p.β ↔
      ¬ ∀ r < p.ℓ, normRq [VG.Proof.MlDsa.Sign.zF p S1 ρ'' κ c r] < p.γ₁ - p.β := by
    rw [← VG.Proof.MlDsa.Sign.normRq_range_lt _ hp.pos₁]; omega
  have c2 : normR ((List.range p.k).map ((fun ri => Vector.map (lowBits p.γ₂) ri) ∘ VG.Proof.MlDsa.Sign.w'F p A S2 ρ'' κ c)) ≥
      p.γ₂ - p.β ↔ ¬ ∀ i < p.k, normRq [VG.Proof.MlDsa.Sign.r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β := by
    rw [ge_iff_le, ← Nat.not_lt, VG.Proof.MlDsa.Sign.normR_lt_iff _ hp.pos₂]
    simp only [List.mem_map, List.mem_range, Function.comp, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, VG.Proof.MlDsa.Sign.r0F, VG.Proof.MlDsa.Sign.normR_lowBits hp.γ₂]
  have c3 : normRq ((List.range p.k).map (VG.Proof.MlDsa.Sign.ct0F T0 c)) ≥ p.γ₂ ↔ ¬ ∀ i < p.k, normRq [VG.Proof.MlDsa.Sign.ct0F T0 c i] < p.γ₂ := by
    rw [← VG.Proof.MlDsa.Sign.normRq_range_lt _ hγ₂]; omega
  have c4 : ((List.range p.k).map (VG.Proof.MlDsa.Sign.hF p A S2 T0 ρ'' κ c)).map (fun hi => (hi.toList.filter id).length) =
      (List.range p.k).map fun i => hintOnes [VG.Proof.MlDsa.Sign.hF p A S2 T0 ρ'' κ c i] := by
    simp only [List.map_map, VG.Proof.MlDsa.Sign.hintOnes_single]; rfl
  rw [c4]
  by_cases h1 : ∀ r < p.ℓ, normRq [VG.Proof.MlDsa.Sign.zF p S1 ρ'' κ c r] < p.γ₁ - p.β
  · by_cases h2 : ∀ i < p.k, normRq [VG.Proof.MlDsa.Sign.r0F p A S2 ρ'' κ c i] < p.γ₂ - p.β
    · by_cases h3 : ∀ i < p.k, normRq [VG.Proof.MlDsa.Sign.ct0F T0 c i] < p.γ₂
      · by_cases h4 : ((List.range p.k).map fun i => hintOnes [VG.Proof.MlDsa.Sign.hF p A S2 T0 ρ'' κ c i]).sum ≤ p.ω
        · rw [VG.Proof.MlDsa.Sign.ifn (by rw [c1, c2, c3]; rintro (h | h | h | h); exacts [h h1, h h2, h h3, by omega]),
            VG.Proof.MlDsa.Sign.ifp (show VG.Proof.MlDsa.Sign.passF p A S1 S2 T0 ρ'' κ c from ⟨h1, h2, h3, h4⟩)]
        · rw [VG.Proof.MlDsa.Sign.ifp (by rw [c1, c2, c3]; exact .inr (.inr (.inr (by omega)))), VG.Proof.MlDsa.Sign.ifn (fun h => h4 h.2.2.2)]
      · rw [VG.Proof.MlDsa.Sign.ifp (by rw [c1, c2, c3]; exact .inr (.inr (.inl h3))), VG.Proof.MlDsa.Sign.ifn (fun h => h3 h.2.2.1)]
    · rw [VG.Proof.MlDsa.Sign.ifp (by rw [c1, c2, c3]; exact .inr (.inl h2)), VG.Proof.MlDsa.Sign.ifn (fun h => h2 h.2.1)]
  · rw [VG.Proof.MlDsa.Sign.ifp (by rw [c1, c2, c3]; exact .inl h1), VG.Proof.MlDsa.Sign.ifn (fun h => h1 h.1)]

end

/-- An iteration of the signing loop, polynomial by polynomial. -/
theorem signIteration_eqF {p : Params} (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (b : Bounds) (A : Nat → Nat → Poly) (S1 S2 T0 : Nat → Poly)
    (μ ρ'' : List Byte) (κ : Nat) :
    signIteration p b (VG.Proof.MlDsa.Sign.amat p A) ((List.range p.ℓ).map S1) ((List.range p.k).map S2) ((List.range p.k).map T0)
      μ ρ'' κ =
      (sampleInBall p.τ b.ball (VG.Proof.MlDsa.Sign.ctF p A μ ρ'' κ)).map fun c =>
        (VG.Proof.MlDsa.Sign.ctF p A μ ρ'' κ, if VG.Proof.MlDsa.Sign.passF p A S1 S2 T0 ρ'' κ c then
          some ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.zF p S1 ρ'' κ c), (List.range p.k).map (VG.Proof.MlDsa.Sign.hF p A S2 T0 ρ'' κ c)) else none) := by
  rw [VG.Proof.MlDsa.Sign.signIteration_eq, VG.Proof.MlDsa.Sign.signCommit_eq]
  dsimp only
  congr 1
  funext c
  rw [VG.Proof.MlDsa.Sign.iterOut_eq p A S1 S2 T0 ρ'' κ c hp]

end VG.Proof.MlDsa.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sign.Leak`. -/
section

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
how the iteration ended (0: rejected, 1: passed, nothing: `SampleInBall`
did not finish), which determines the structure of the loop: two runs that
agree on it agree on each `c̃`, on the outcome of each iteration and on the
hint of the one that passes (`leakT_step`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

/-- `signLeakLoop`, with the outcome of each iteration after its `c̃`: 0 if
it is rejected, 1 (then its hint) if it passes. -/
def signLeakLoopT (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) : (iters κ : Nat) → List Nat
  | 0, _ => []
  | iters + 1, κ =>
    leakBytes (signCommit p Â μ ρ'' κ).2.2 ++
      match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
      | some (_, none) => 0 :: VG.Proof.MlDsa.Sign.signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters (κ + p.ℓ)
      | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
      | none => []

/-- `signLeak`, with `signLeakLoopT` for `signLeakLoop`. -/
def signLeakT (p : Params) (sk μ rnd : List Byte) : List Nat :=
  let (ρ, K, _tr, s₁, s₂, t₀) := skDecode p sk
  leakBytes ρ ++
    match expandA p maxBounds ρ with
    | none => []
    | some Â =>
      VG.Proof.MlDsa.Sign.signLeakLoopT p maxBounds Â (s₁.map fun s => ntt (toRq s)) (s₂.map fun s => ntt (toRq s))
        (t₀.map fun t => ntt (toRq t)) μ (H (K ++ rnd ++ μ) 64) maxBounds.sign 0

/-- `signLeakLoopT` is the contract's `signLeakLoop`, which tags each
iteration the same way. -/
theorem signLeakLoopT_eq_signLeakLoop (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) : ∀ iters κ,
    VG.Proof.MlDsa.Sign.signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ = signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ
  | 0, _ => rfl
  | iters + 1, κ => by
    have ih := VG.Proof.MlDsa.Sign.signLeakLoopT_eq_signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters (κ + p.ℓ)
    unfold VG.Proof.MlDsa.Sign.signLeakLoopT signLeakLoop
    cases signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
    | none => rfl
    | some r =>
      rcases r with ⟨_, _ | _⟩
      · exact congrArg (_ ++ 0 :: ·) ih
      · rfl

/-- `signLeakT` is the contract's `signLeak`. -/
theorem signLeakT_eq_signLeak (p : Params) (sk μ rnd : List Byte) : VG.Proof.MlDsa.Sign.signLeakT p sk μ rnd = signLeak p sk μ rnd := by
  have h : @VG.Proof.MlDsa.Sign.signLeakLoopT = @signLeakLoop := by
    funext p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ
    exact VG.Proof.MlDsa.Sign.signLeakLoopT_eq_signLeakLoop p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' iters κ
  unfold VG.Proof.MlDsa.Sign.signLeakT signLeak
  simp only [h]
  -- The two sides differ only in their `match` auxiliaries, which are equal.
  cases expandA p maxBounds (skDecode p sk).fst <;> rfl

theorem leakBytes_inj : ∀ {a b : List Byte}, leakBytes a = leakBytes b → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [leakBytes, List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.MlDsa.Sign.leakBytes_inj h.2]
  | [], _ :: _, h => by simp [leakBytes] at h
  | _ :: _, [], h => by simp [leakBytes] at h

theorem leakBytes_length (a : List Byte) : (leakBytes a).length = a.length := List.length_map _

/-- How an iteration ended, as `signLeakLoopT` lists it after its `c̃`. -/
def outTag : Option (List Byte × Option (List Poly × List (Vector Bool n))) → List Nat
  | some (_, none) => [0]
  | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
  | none => []

theorem signCommit_length (p : Params) (Â : List (List Poly)) (μ ρ'' : List Byte) (κ : Nat) :
    (signCommit p Â μ ρ'' κ).2.2.length = p.ctildeLen := VG.Proof.MlDsa.Sign.H_length _ _

section
variable {p : Params} {b : Bounds}
  {Â₁ Â₂ : List (List Poly)} {s₁ s₁' t₁ s₂ s₂' t₂ : List Poly} {μ₁ μ₂ ρ₁ ρ₂ : List Byte}

/-- Two runs that agree on what an iteration leaks agree on its `c̃`, on
whether it finished, was rejected or passed, and on the hint if it passed;
and, if it was rejected, on what the following iterations leak. -/
theorem leakT_step {n κ : Nat}
    (h : VG.Proof.MlDsa.Sign.signLeakLoopT p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ (n + 1) κ = VG.Proof.MlDsa.Sign.signLeakLoopT p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ (n + 1) κ) :
    (signCommit p Â₁ μ₁ ρ₁ κ).2.2 = (signCommit p Â₂ μ₂ ρ₂ κ).2.2 ∧
      ((∃ ct, signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ = some (ct, none)) →
        (∃ ct, signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ = some (ct, none)) ∧
        VG.Proof.MlDsa.Sign.signLeakLoopT p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ n (κ + p.ℓ) = VG.Proof.MlDsa.Sign.signLeakLoopT p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ n (κ + p.ℓ)) ∧
      VG.Proof.MlDsa.Sign.outTag (signIteration p b Â₁ s₁ s₁' t₁ μ₁ ρ₁ κ) = VG.Proof.MlDsa.Sign.outTag (signIteration p b Â₂ s₂ s₂' t₂ μ₂ ρ₂ κ) := by
  simp only [VG.Proof.MlDsa.Sign.signLeakLoopT] at h
  have hl : (leakBytes (signCommit p Â₁ μ₁ ρ₁ κ).2.2).length = (leakBytes (signCommit p Â₂ μ₂ ρ₂ κ).2.2).length := by
    rw [VG.Proof.MlDsa.Sign.leakBytes_length, VG.Proof.MlDsa.Sign.leakBytes_length, VG.Proof.MlDsa.Sign.signCommit_length, VG.Proof.MlDsa.Sign.signCommit_length]
  obtain ⟨hc, hr⟩ := List.append_inj h hl
  refine ⟨VG.Proof.MlDsa.Sign.leakBytes_inj hc, ?_, ?_⟩
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
      | some zh => cases (List.cons.inj hr).1
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
          | some _ => intro hr; cases (List.cons.inj hr).1
        | some zh =>
          cases o' with
          | none => intro hr; cases (List.cons.inj hr).1
          | some zh' => intro hr; simp only [VG.Proof.MlDsa.Sign.outTag]; exact hr

end

theorem signLeakLoopT_succ (p : Params) (b : Bounds) (Â : List (List Poly)) (ŝ₁ ŝ₂ t₀Hat : List Poly)
    (μ ρ'' : List Byte) (n κ : Nat) :
    VG.Proof.MlDsa.Sign.signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' (n + 1) κ =
      leakBytes (signCommit p Â μ ρ'' κ).2.2 ++
        match signIteration p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' κ with
        | some (_, none) => 0 :: VG.Proof.MlDsa.Sign.signLeakLoopT p b Â ŝ₁ ŝ₂ t₀Hat μ ρ'' n (κ + p.ℓ)
        | some (_, some (_, h)) => 1 :: h.flatMap fun hi => hi.toList.map Bool.toNat
        | none => [] := rfl

end VG.Proof.MlDsa.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sign.Setup`. -/
section

/-!
# ML-DSA: signing's matrix and private key, polynomial by polynomial

The vectors that `skDecode` gives, transformed by `NTT` as `Sign_internal`
uses them, are `List.range` mapped by a function of the index of the piece of
the private key (`skS1_eq`, `skS2_eq`, `skT0_eq`); `ExpandA` is the matrix of
its entries if each `RejNTTPoly` finishes (`expandA_some`), and fails if one
does not (`expandA_none`). With them, `signMu` and `signLeakT` in terms of the
loop (`signMu_some`, `signMu_none_A`, `signMu_none_L`, `signLeakT_eq`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

/-! ## The private key -/

section
variable (p : Params) (sk : List Byte)

/-- The length of the encoding of a polynomial of `s₁` or `s₂`. -/
abbrev lenS : Nat := 32 * bitlen (2 * p.η)

/-- `ŝ₁[r] = NTT(BitUnpack(sk[128 + lenS·r : …], η, η))`. -/
def s1F (r : Nat) : Poly := ntt (toRq (bitUnpack ((sk.drop (128 + VG.Proof.MlDsa.Sign.lenS p * r)).take (VG.Proof.MlDsa.Sign.lenS p)) p.η p.η))

/-- `ŝ₂[i]`. -/
def s2F (i : Nat) : Poly :=
  ntt (toRq (bitUnpack ((sk.drop (128 + VG.Proof.MlDsa.Sign.lenS p * p.ℓ + VG.Proof.MlDsa.Sign.lenS p * i)).take (VG.Proof.MlDsa.Sign.lenS p)) p.η p.η))

/-- `t̂₀[i]`. -/
def t0F (i : Nat) : Poly :=
  ntt (toRq (bitUnpack ((sk.drop (128 + VG.Proof.MlDsa.Sign.lenS p * p.ℓ + VG.Proof.MlDsa.Sign.lenS p * p.k + 32 * d * i)).take (32 * d))
    (2 ^ (d - 1) - 1) (2 ^ (d - 1))))

theorem skS1_eq : (skDecode p sk).2.2.2.1.map (fun s => ntt (toRq s)) = (List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk) := by
  simp only [skDecode, pieces, List.map_map]; rfl

theorem skS2_eq : (skDecode p sk).2.2.2.2.1.map (fun s => ntt (toRq s)) = (List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk) := by
  simp only [skDecode, pieces, List.map_map]; rfl

theorem skT0_eq : (skDecode p sk).2.2.2.2.2.map (fun s => ntt (toRq s)) = (List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk) := by
  simp only [skDecode, pieces, List.map_map]; rfl

theorem skRho_eq : (skDecode p sk).1 = sk.take 32 := rfl

theorem skK_eq : (skDecode p sk).2.1 = (sk.drop 32).take 32 := rfl

end

/-! ## `ExpandA` -/

/-- The seed `ρ ‖ IntegerToBytes(j, 1) ‖ IntegerToBytes(i, 1)` of `Â[i, j]`. -/
def aSeed (ρ : List Byte) (i j : Nat) : List Byte := ρ ++ integerToBytes j 1 ++ integerToBytes i 1

/-- `Â[i, j]`, if its `RejNTTPoly` finishes within `bound` bytes. -/
def aF (bound : Nat) (ρ : List Byte) (i j : Nat) : Poly := (rejNTTPoly bound (VG.Proof.MlDsa.Sign.aSeed ρ i j)).getD zero

theorem mapM_eq_some_of {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x (List.mem_cons_self ..), VG.Proof.MlDsa.Sign.mapM_eq_some_of fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem mapM_eq_none_of {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∃ x ∈ l, f x = none) → l.mapM f = none
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | x :: l, ⟨y, hy, hn⟩ => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hn]; rfl
    · cases f x with
      | none => rfl
      | some _ => simp only [Option.bind_eq_bind, Option.bind_some]; rw [VG.Proof.MlDsa.Sign.mapM_eq_none_of ⟨y, hy, hn⟩]; rfl

theorem expandA_some {p : Params} {b : Bounds} {ρ : List Byte}
    (h : ∀ i < p.k, ∀ j < p.ℓ, (rejNTTPoly b.rejNTT (VG.Proof.MlDsa.Sign.aSeed ρ i j)).isSome) :
    expandA p b ρ = some (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.aF b.rejNTT ρ)) := by
  unfold expandA VG.Proof.MlDsa.Sign.amat
  refine VG.Proof.MlDsa.Sign.mapM_eq_some_of fun i hi => VG.Proof.MlDsa.Sign.mapM_eq_some_of fun j hj => ?_
  rw [List.mem_range] at hi hj
  have := h i hi j hj
  unfold VG.Proof.MlDsa.Sign.aF
  show rejNTTPoly b.rejNTT (VG.Proof.MlDsa.Sign.aSeed ρ i j) = some ((rejNTTPoly b.rejNTT (VG.Proof.MlDsa.Sign.aSeed ρ i j)).getD zero)
  cases e : rejNTTPoly b.rejNTT (VG.Proof.MlDsa.Sign.aSeed ρ i j) with
  | none => rw [e] at this; cases this
  | some x => rfl

theorem expandA_none {p : Params} {b : Bounds} {ρ : List Byte}
    (h : ∃ i < p.k, ∃ j < p.ℓ, rejNTTPoly b.rejNTT (VG.Proof.MlDsa.Sign.aSeed ρ i j) = none) : expandA p b ρ = none := by
  obtain ⟨i, hi, j, hj, hn⟩ := h
  exact VG.Proof.MlDsa.Sign.mapM_eq_none_of ⟨i, List.mem_range.mpr hi, VG.Proof.MlDsa.Sign.mapM_eq_none_of ⟨j, List.mem_range.mpr hj, hn⟩⟩

/-! ## `Sign_internal` -/

section
variable {p : Params} {sk μ rnd : List Byte}

/-- The signature, from the loop's result. -/
def sigOf (p : Params) (r : List Byte × List Poly × List (Vector Bool n)) : List Byte :=
  sigEncode p r.1 (r.2.1.map fun zi => zi.map fun c => modPm c.val q) r.2.2

theorem signMu_some {b : Bounds} {Â : List (List Poly)} (hA : expandA p b (sk.take 32) = some Â)
    {r : List Byte × List Poly × List (Vector Bool n)}
    (hL : signLoop p b Â ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk))
      ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk)) μ (H ((sk.drop 32).take 32 ++ rnd ++ μ) 64) b.sign 0 = some r) :
    signMu p b sk μ rnd = some (VG.Proof.MlDsa.Sign.sigOf p r) := by
  rw [VG.Proof.MlDsa.Sign.signMu_eq, VG.Proof.MlDsa.Sign.skRho_eq, hA, Option.bind_some, VG.Proof.MlDsa.Sign.skS1_eq, VG.Proof.MlDsa.Sign.skS2_eq, VG.Proof.MlDsa.Sign.skT0_eq, VG.Proof.MlDsa.Sign.skK_eq, hL]; rfl

theorem signMu_none_A {b : Bounds} (hA : expandA p b (sk.take 32) = none) : signMu p b sk μ rnd = none := by
  rw [VG.Proof.MlDsa.Sign.signMu_eq, VG.Proof.MlDsa.Sign.skRho_eq, hA]; rfl

theorem signMu_none_L {b : Bounds} {Â : List (List Poly)} (hA : expandA p b (sk.take 32) = some Â)
    (hL : signLoop p b Â ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk))
      ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk)) μ (H ((sk.drop 32).take 32 ++ rnd ++ μ) 64) b.sign 0 = none) :
    signMu p b sk μ rnd = none := by
  rw [VG.Proof.MlDsa.Sign.signMu_eq, VG.Proof.MlDsa.Sign.skRho_eq, hA, Option.bind_some, VG.Proof.MlDsa.Sign.skS1_eq, VG.Proof.MlDsa.Sign.skS2_eq, VG.Proof.MlDsa.Sign.skT0_eq, VG.Proof.MlDsa.Sign.skK_eq, hL]; rfl

/-- What signing leaks, once `ExpandA` finishes. -/
theorem signLeakT_eq {Â : List (List Poly)} (hA : expandA p maxBounds (sk.take 32) = some Â) :
    VG.Proof.MlDsa.Sign.signLeakT p sk μ rnd = leakBytes (sk.take 32) ++
      VG.Proof.MlDsa.Sign.signLeakLoopT p maxBounds Â ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk))
        ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk)) μ (H ((sk.drop 32).take 32 ++ rnd ++ μ) 64) maxBounds.sign 0 := by
  have h1 := VG.Proof.MlDsa.Sign.skS1_eq p sk
  have h2 := VG.Proof.MlDsa.Sign.skS2_eq p sk
  have h3 := VG.Proof.MlDsa.Sign.skT0_eq p sk
  unfold VG.Proof.MlDsa.Sign.signLeakT
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  rw [e] at h1 h2 h3
  have hρ : ρ = sk.take 32 := by rw [← VG.Proof.MlDsa.Sign.skRho_eq p sk, e]
  have hK : K = (sk.drop 32).take 32 := by rw [← VG.Proof.MlDsa.Sign.skK_eq p sk, e]
  dsimp only at h1 h2 h3 ⊢
  subst hρ hK
  rw [hA, h1, h2, h3]

end

end VG.Proof.MlDsa.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Sign.Vals`. -/
section

/-!
# ML-DSA: signing's values, from its inputs

What signing computes, as functions of its inputs `sk`, `μ` and `rnd` (`Av`,
`ctV`, `cV`, `passV`, `zV`, `hV`, …), for an implementation that computes them
one polynomial at a time; and the loop of an implementation whose
`SampleInBall` succeeds exactly when `ballF` says, and which succeeds only
when the algorithm finishes within `maxBounds` (`BallF`): iteration `t`
continues the loop (`contV`) if its `SampleInBall` succeeded and its checks
failed, and the loop runs `nIt contV 814` iterations.

Two runs whose `signLeakT` agree agree on `ρ` (`rho_of_leak`), and, once
`ExpandA` finishes, on what each iteration they both reach leaks
(`leak_iter`): its `c̃`, whether its checks passed, and then its hint.
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

/-! ## The number of iterations -/

/-- The number of iterations of a loop of at most `M` iterations that
continues after iteration `t` while `f t`. -/
def nIt (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | M + 1 => if (List.range M).all f then M + 1 else VG.Proof.MlDsa.Sign.nIt f M

theorem nIt_le (f : Nat → Bool) : ∀ M, VG.Proof.MlDsa.Sign.nIt f M ≤ M
  | 0 => Nat.le_refl _
  | M + 1 => by
    unfold VG.Proof.MlDsa.Sign.nIt
    split
    · exact Nat.le_refl _
    · have := VG.Proof.MlDsa.Sign.nIt_le f M; omega

theorem nIt_pos (f : Nat → Bool) : ∀ {M}, 0 < M → 0 < VG.Proof.MlDsa.Sign.nIt f M
  | 0, h => absurd h (Nat.lt_irrefl _)
  | M + 1, _ => by
    unfold VG.Proof.MlDsa.Sign.nIt
    split
    · omega
    · rename_i h
      cases M with
      | zero => exact absurd (by simp) h
      | succ M => exact VG.Proof.MlDsa.Sign.nIt_pos f (Nat.succ_pos M)

theorem nIt_cont (f : Nat → Bool) : ∀ {M j}, j + 1 < VG.Proof.MlDsa.Sign.nIt f M → f j = true
  | 0, _, h => absurd h (by simp [VG.Proof.MlDsa.Sign.nIt])
  | M + 1, j, h => by
    unfold VG.Proof.MlDsa.Sign.nIt at h
    split at h
    · rename_i ha
      exact List.all_eq_true.mp ha j (List.mem_range.mpr (by omega))
    · exact VG.Proof.MlDsa.Sign.nIt_cont f h

theorem nIt_stop (f : Nat → Bool) : ∀ {M k}, k + 1 = VG.Proof.MlDsa.Sign.nIt f M → k + 1 < M → f k = false
  | 0, _, h, _ => absurd h (by simp [VG.Proof.MlDsa.Sign.nIt])
  | M + 1, k, h, hk => by
    unfold VG.Proof.MlDsa.Sign.nIt at h
    split at h
    · omega
    · rename_i ha
      rcases (by omega : k + 1 < M ∨ k + 1 = M) with hk' | hk'
      · exact VG.Proof.MlDsa.Sign.nIt_stop f h hk'
      · subst hk'
        -- `nIt f (k + 1) = k + 1`: either every iteration before `k` continued, or not.
        cases e : f k with
        | false => rfl
        | true =>
          refine absurd ?_ ha
          rw [List.all_eq_true]
          intro j hj
          rw [List.mem_range] at hj
          rcases (by omega : j < k ∨ j = k) with hj | rfl
          · have h2 := h
            unfold VG.Proof.MlDsa.Sign.nIt at h2
            split at h2
            · rename_i hb; exact List.all_eq_true.mp hb j (List.mem_range.mpr hj)
            · have := VG.Proof.MlDsa.Sign.nIt_le f k; omega
          · exact e

/-- Whether iteration `k < nIt f M` is followed by another one. -/
theorem nIt_next (f : Nat → Bool) {M k : Nat} (hk : k < VG.Proof.MlDsa.Sign.nIt f M) :
    k + 1 < VG.Proof.MlDsa.Sign.nIt f M ↔ f k = true ∧ k + 1 < M := by
  have hle := VG.Proof.MlDsa.Sign.nIt_le f M
  constructor
  · intro h; exact ⟨VG.Proof.MlDsa.Sign.nIt_cont f h, by omega⟩
  · rintro ⟨hf, hM⟩
    by_contra hn
    have := VG.Proof.MlDsa.Sign.nIt_stop f (show k + 1 = VG.Proof.MlDsa.Sign.nIt f M by omega) hM
    rw [hf] at this; cases this

/-- The iterations before one reached continued. -/
theorem nIt_before (f : Nat → Bool) {M k : Nat} (hk : k < VG.Proof.MlDsa.Sign.nIt f M) : ∀ j < k, f j = true :=
  fun j hj => VG.Proof.MlDsa.Sign.nIt_cont f (M := M) (by omega)

/-- Two loops that continue alike as long as either does run as many iterations. -/
theorem nIt_congr {f g : Nat → Bool} {N : Nat}
    (hfg : ∀ M < N, (∀ j < M, f j = true) → ∀ j < M, g j = true)
    (hgf : ∀ M < N, (∀ j < M, g j = true) → ∀ j < M, f j = true) : VG.Proof.MlDsa.Sign.nIt f N = VG.Proof.MlDsa.Sign.nIt g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold VG.Proof.MlDsa.Sign.nIt
    rw [ih (fun M hM => hfg M (by omega)) (fun M hM => hgf M (by omega))]
    have e : (List.range N).all f = (List.range N).all g := by
      cases e : (List.range N).all f with
      | true =>
        have := hfg N (by omega) fun j hj => List.all_eq_true.mp e j (List.mem_range.mpr hj)
        exact (List.all_eq_true.mpr fun j hj => this j (List.mem_range.mp hj)).symm
      | false =>
        cases e' : (List.range N).all g with
        | false => rfl
        | true =>
          have := hgf N (by omega) fun j hj => List.all_eq_true.mp e' j (List.mem_range.mpr hj)
          rw [List.all_eq_true.mpr fun j hj => this j (List.mem_range.mp hj)] at e
          cases e
    rw [e]

/-! ## The values -/

section
variable (p : Params) (sk mu rnd : List Byte)

/-- `ρ`. -/
abbrev rhoV : List Byte := sk.take 32
/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppV : List Byte := H ((sk.drop 32).take 32 ++ rnd ++ mu) 64
/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Av : Nat → Nat → Poly := VG.Proof.MlDsa.Sign.aF maxBounds.rejNTT (VG.Proof.MlDsa.Sign.rhoV sk)

/-- The arguments of `signLoop`. -/
abbrev loopV (b : Bounds) (n κ : Nat) : Option (List Byte × List Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.Av sk)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk))
    ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk)) mu (VG.Proof.MlDsa.Sign.rppV sk mu rnd) n κ

abbrev iterV (b : Bounds) (κ : Nat) : Option (List Byte × Option (List Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.Av sk)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk))
    ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk)) mu (VG.Proof.MlDsa.Sign.rppV sk mu rnd) κ

/-- What the loop leaks. -/
abbrev leakV : List Nat :=
  VG.Proof.MlDsa.Sign.signLeakLoopT p maxBounds (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.Av sk)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk))
    ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk)) mu (VG.Proof.MlDsa.Sign.rppV sk mu rnd) maxBounds.sign 0

/-- `c̃` of the iteration with counter `κ`. -/
abbrev ctV (κ : Nat) : List Byte := VG.Proof.MlDsa.Sign.ctF p (VG.Proof.MlDsa.Sign.Av sk) mu (VG.Proof.MlDsa.Sign.rppV sk mu rnd) κ
/-- `c = SampleInBall(c̃)`, within `maxBounds`. -/
abbrev cV (κ : Nat) : IPoly := (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ)).getD (Vector.replicate n 0)
/-- The validity checks pass. -/
abbrev passV (κ : Nat) : Prop :=
  VG.Proof.MlDsa.Sign.passF p (VG.Proof.MlDsa.Sign.Av sk) (VG.Proof.MlDsa.Sign.s1F p sk) (VG.Proof.MlDsa.Sign.s2F p sk) (VG.Proof.MlDsa.Sign.t0F p sk) (VG.Proof.MlDsa.Sign.rppV sk mu rnd) κ (VG.Proof.MlDsa.Sign.cV p sk mu rnd κ)
abbrev zV (κ : Nat) : Nat → Poly := VG.Proof.MlDsa.Sign.zF p (VG.Proof.MlDsa.Sign.s1F p sk) (VG.Proof.MlDsa.Sign.rppV sk mu rnd) κ (VG.Proof.MlDsa.Sign.cV p sk mu rnd κ)
abbrev hV (κ : Nat) : Nat → Vector Bool n :=
  VG.Proof.MlDsa.Sign.hF p (VG.Proof.MlDsa.Sign.Av sk) (VG.Proof.MlDsa.Sign.s2F p sk) (VG.Proof.MlDsa.Sign.t0F p sk) (VG.Proof.MlDsa.Sign.rppV sk mu rnd) κ (VG.Proof.MlDsa.Sign.cV p sk mu rnd κ)
/-- The hint of the iteration with counter `κ`, as the list of its coefficients. -/
abbrev hbitsV (κ : Nat) : List Nat := ((List.range p.k).map (VG.Proof.MlDsa.Sign.hV p sk mu rnd κ)).flatMap fun hi => hi.toList.map Bool.toNat

/-- The `t` iterations from counter 0 are rejected within `maxBounds`. -/
abbrev RejV (t : Nat) : Prop :=
  VG.Proof.MlDsa.Sign.Rej p (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.Av sk)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk))
    ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk)) mu (VG.Proof.MlDsa.Sign.rppV sk mu rnd) maxBounds 0 t

end

/-- An implementation's `SampleInBall` on `(τ, c̃)` succeeds exactly when
`ballF τ c̃`, and then within `maxBounds`. -/
def BallF (ballF : Nat → List Byte → Bool) : Prop :=
  ∀ τ B, ballF τ B = true → (sampleInBall τ maxBounds.ball B).isSome

section
variable (p : Params) (sk mu rnd : List Byte) (ballF : Nat → List Byte → Bool)

/-- Iteration `t` continues the loop: its `SampleInBall` succeeded and its checks failed. -/
def contV (t : Nat) : Bool := ballF p.τ (VG.Proof.MlDsa.Sign.ctV p sk mu rnd (p.ℓ * t)) && !decide (VG.Proof.MlDsa.Sign.passV p sk mu rnd (p.ℓ * t))

/-- The number of iterations the implementation runs. -/
abbrev itV : Nat := VG.Proof.MlDsa.Sign.nIt (VG.Proof.MlDsa.Sign.contV p sk mu rnd ballF) 814

end

/-! ## The iterations -/

section
variable {p : Params} {sk mu rnd : List Byte} {κ : Nat}

theorem cV_eq (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ)).isSome) :
    sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ) = some (VG.Proof.MlDsa.Sign.cV p sk mu rnd κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [VG.Proof.MlDsa.Sign.cV, hc, Option.getD_some]

theorem iterV_eq (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (b : Bounds) :
    VG.Proof.MlDsa.Sign.iterV p sk mu rnd b κ = (sampleInBall p.τ b.ball (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ)).map fun c =>
      (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ, if VG.Proof.MlDsa.Sign.passF p (VG.Proof.MlDsa.Sign.Av sk) (VG.Proof.MlDsa.Sign.s1F p sk) (VG.Proof.MlDsa.Sign.s2F p sk) (VG.Proof.MlDsa.Sign.t0F p sk) (VG.Proof.MlDsa.Sign.rppV sk mu rnd) κ c then
        some ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.zF p (VG.Proof.MlDsa.Sign.s1F p sk) (VG.Proof.MlDsa.Sign.rppV sk mu rnd) κ c),
          (List.range p.k).map (VG.Proof.MlDsa.Sign.hF p (VG.Proof.MlDsa.Sign.Av sk) (VG.Proof.MlDsa.Sign.s2F p sk) (VG.Proof.MlDsa.Sign.t0F p sk) (VG.Proof.MlDsa.Sign.rppV sk mu rnd) κ c)) else none) :=
  VG.Proof.MlDsa.Sign.signIteration_eqF hp b _ _ _ _ _ _ κ

theorem iterV_rej (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ)).isSome)
    (hf : ¬ VG.Proof.MlDsa.Sign.passV p sk mu rnd κ) : VG.Proof.MlDsa.Sign.iterV p sk mu rnd maxBounds κ = some (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ, none) := by
  rw [VG.Proof.MlDsa.Sign.iterV_eq hp, VG.Proof.MlDsa.Sign.cV_eq h, Option.map_some, VG.Proof.MlDsa.Sign.ifn hf]

theorem iterV_pass (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ)).isSome)
    (hf : VG.Proof.MlDsa.Sign.passV p sk mu rnd κ) : VG.Proof.MlDsa.Sign.iterV p sk mu rnd maxBounds κ =
      some (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ, some ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.zV p sk mu rnd κ), (List.range p.k).map (VG.Proof.MlDsa.Sign.hV p sk mu rnd κ))) := by
  rw [VG.Proof.MlDsa.Sign.iterV_eq hp, VG.Proof.MlDsa.Sign.cV_eq h, Option.map_some, VG.Proof.MlDsa.Sign.ifp hf]

theorem iterV_none (h : sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.Sign.ctV p sk mu rnd κ) = none) :
    VG.Proof.MlDsa.Sign.iterV p sk mu rnd minBounds κ = none := by
  rw [VG.Proof.MlDsa.Sign.iterV, VG.Proof.MlDsa.Sign.signIteration_eq, VG.Proof.MlDsa.Sign.signCommit_eq, h]; rfl

variable {ballF : Nat → List Byte → Bool}

/-- Iterations that continued were rejected within `maxBounds`. -/
theorem rejV_of (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (hb : VG.Proof.MlDsa.Sign.BallF ballF) {t : Nat}
    (h : ∀ j < t, VG.Proof.MlDsa.Sign.contV p sk mu rnd ballF j = true) : VG.Proof.MlDsa.Sign.RejV p sk mu rnd t := by
  intro j hj
  have hc := h j hj
  simp only [VG.Proof.MlDsa.Sign.contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
  exact ⟨_, by rw [Nat.zero_add]; exact VG.Proof.MlDsa.Sign.iterV_rej hp (hb _ _ hc.1) hc.2⟩

theorem loopV_pass (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (hb : VG.Proof.MlDsa.Sign.BallF ballF) {t : Nat} (ht : t < maxBounds.sign)
    (h : ∀ j < t, VG.Proof.MlDsa.Sign.contV p sk mu rnd ballF j = true) (hs : ballF p.τ (VG.Proof.MlDsa.Sign.ctV p sk mu rnd (p.ℓ * t)) = true)
    (hpass : VG.Proof.MlDsa.Sign.passV p sk mu rnd (p.ℓ * t)) :
    VG.Proof.MlDsa.Sign.loopV p sk mu rnd maxBounds maxBounds.sign 0 =
      some (VG.Proof.MlDsa.Sign.ctV p sk mu rnd (p.ℓ * t), (List.range p.ℓ).map (VG.Proof.MlDsa.Sign.zV p sk mu rnd (p.ℓ * t)),
        (List.range p.k).map (VG.Proof.MlDsa.Sign.hV p sk mu rnd (p.ℓ * t))) :=
  VG.Proof.MlDsa.Sign.signLoop_pass _ _ _ _ _ _ _ (VG.Proof.MlDsa.Sign.rejV_of hp hb h) ht (VG.Proof.MlDsa.Sign.iterV_pass hp (hb _ _ hs) hpass)

theorem loopV_none_ball (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (hb : VG.Proof.MlDsa.Sign.BallF ballF) {t : Nat}
    (h : ∀ j < t, VG.Proof.MlDsa.Sign.contV p sk mu rnd ballF j = true)
    (hn : sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.Sign.ctV p sk mu rnd (p.ℓ * t)) = none) :
    VG.Proof.MlDsa.Sign.loopV p sk mu rnd minBounds minBounds.sign 0 = none :=
  VG.Proof.MlDsa.Sign.signLoop_min_none p _ _ _ _ _ _ (by decide) (VG.Proof.MlDsa.Sign.rejV_of hp hb h)
    (.inr (by rw [Nat.zero_add]; exact VG.Proof.MlDsa.Sign.iterV_none hn))

theorem loopV_none_exh (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (hb : VG.Proof.MlDsa.Sign.BallF ballF) (h : ∀ j < 814, VG.Proof.MlDsa.Sign.contV p sk mu rnd ballF j = true) :
    VG.Proof.MlDsa.Sign.loopV p sk mu rnd minBounds minBounds.sign 0 = none :=
  VG.Proof.MlDsa.Sign.signLoop_min_none p _ _ _ _ _ _ (by decide) (VG.Proof.MlDsa.Sign.rejV_of hp hb h) (.inl (by decide))

end

/-! ## What two runs leak -/

section
variable {p : Params} {sk mu rnd sk' mu' rnd' : List Byte}

theorem signLeakT_take (hl : 32 ≤ sk.length) : (VG.Proof.MlDsa.Sign.signLeakT p sk mu rnd).take 32 = leakBytes (sk.take 32) := by
  unfold VG.Proof.MlDsa.Sign.signLeakT
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← VG.Proof.MlDsa.Sign.skRho_eq p sk, e]
  dsimp only
  subst hρ
  have hlen : (leakBytes (sk.take 32)).length = 32 := by rw [VG.Proof.MlDsa.Sign.leakBytes_length, List.length_take]; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem rho_of_leak (hl : 32 ≤ sk.length) (hl' : 32 ≤ sk'.length)
    (h : VG.Proof.MlDsa.Sign.signLeakT p sk mu rnd = VG.Proof.MlDsa.Sign.signLeakT p sk' mu' rnd') : VG.Proof.MlDsa.Sign.rhoV sk = VG.Proof.MlDsa.Sign.rhoV sk' := by
  have := congrArg (List.take 32) h
  rw [VG.Proof.MlDsa.Sign.signLeakT_take hl, VG.Proof.MlDsa.Sign.signLeakT_take hl'] at this
  exact VG.Proof.MlDsa.Sign.leakBytes_inj this

/-- Once `ExpandA` finishes, the loops of two runs whose `signLeakT` agree leak the same. -/
theorem leakV_of_leak (hl : 32 ≤ sk.length) (hl' : 32 ≤ sk'.length)
    (hA : expandA p maxBounds (VG.Proof.MlDsa.Sign.rhoV sk) = some (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.Av sk)))
    (hA' : expandA p maxBounds (VG.Proof.MlDsa.Sign.rhoV sk') = some (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.Av sk')))
    (h : VG.Proof.MlDsa.Sign.signLeakT p sk mu rnd = VG.Proof.MlDsa.Sign.signLeakT p sk' mu' rnd') : VG.Proof.MlDsa.Sign.leakV p sk mu rnd = VG.Proof.MlDsa.Sign.leakV p sk' mu' rnd' := by
  have hr := VG.Proof.MlDsa.Sign.rho_of_leak hl hl' h
  have hr' : sk.take 32 = sk'.take 32 := hr
  rw [VG.Proof.MlDsa.Sign.signLeakT_eq hA, VG.Proof.MlDsa.Sign.signLeakT_eq hA', hr'] at h
  exact List.append_cancel_left h

variable {ballF : Nat → List Byte → Bool}

/-- What two runs whose loops leak the same agree on, at an iteration they both reach. -/
theorem leak_iter (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (hb : VG.Proof.MlDsa.Sign.BallF ballF) (h : VG.Proof.MlDsa.Sign.leakV p sk mu rnd = VG.Proof.MlDsa.Sign.leakV p sk' mu' rnd') :
    ∀ {t : Nat}, t < maxBounds.sign → (∀ j < t, VG.Proof.MlDsa.Sign.contV p sk mu rnd ballF j = true) →
      (∀ j < t, VG.Proof.MlDsa.Sign.contV p sk' mu' rnd' ballF j = true) ∧
      VG.Proof.MlDsa.Sign.signLeakLoopT p maxBounds (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.Av sk)) ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk)) ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk))
          ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk)) mu (VG.Proof.MlDsa.Sign.rppV sk mu rnd) (maxBounds.sign - t) (p.ℓ * t) =
        VG.Proof.MlDsa.Sign.signLeakLoopT p maxBounds (VG.Proof.MlDsa.Sign.amat p (VG.Proof.MlDsa.Sign.Av sk')) ((List.range p.ℓ).map (VG.Proof.MlDsa.Sign.s1F p sk'))
          ((List.range p.k).map (VG.Proof.MlDsa.Sign.s2F p sk')) ((List.range p.k).map (VG.Proof.MlDsa.Sign.t0F p sk')) mu' (VG.Proof.MlDsa.Sign.rppV sk' mu' rnd')
          (maxBounds.sign - t) (p.ℓ * t)
  | 0, _, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), by simpa using h⟩
  | t + 1, ht, hc => by
    obtain ⟨hc', ih⟩ := VG.Proof.MlDsa.Sign.leak_iter hp hb h (t := t) (by omega) fun j hj => hc j (by omega)
    rw [show maxBounds.sign - t = (maxBounds.sign - (t + 1)) + 1 by
      have : maxBounds.sign = 1000 := rfl; omega] at ih
    obtain ⟨_, hrej, _⟩ := VG.Proof.MlDsa.Sign.leakT_step ih
    have c1 := hc t (by omega)
    simp only [VG.Proof.MlDsa.Sign.contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at c1
    obtain ⟨hr', hnext⟩ := hrej ⟨_, VG.Proof.MlDsa.Sign.iterV_rej hp (hb _ _ c1.1) c1.2⟩
    refine ⟨fun j hj => ?_, by rw [show p.ℓ * (t + 1) = p.ℓ * t + p.ℓ by rw [Nat.mul_succ]]; exact hnext⟩
    rcases (by omega : j < t ∨ j = t) with hj | rfl
    · exact hc' j hj
    · obtain ⟨ct, hct⟩ := hr'
      change VG.Proof.MlDsa.Sign.iterV p sk' mu' rnd' maxBounds (p.ℓ * j) = some (ct, none) at hct
      have hct' := hct
      rw [VG.Proof.MlDsa.Sign.iterV_eq hp] at hct'
      obtain ⟨c, hcs, hc2⟩ := Option.map_eq_some_iff.mp hct'
      simp only [Prod.mk.injEq] at hc2
      have hpass : ¬ VG.Proof.MlDsa.Sign.passV p sk' mu' rnd' (p.ℓ * j) := by
        intro hq
        rw [VG.Proof.MlDsa.Sign.iterV_pass hp (by rw [hcs]; rfl) hq] at hct
        cases (Prod.mk.inj (Option.some.inj hct)).2
      -- `ballF` agrees, as `c̃` does.
      have ect : VG.Proof.MlDsa.Sign.ctV p sk mu rnd (p.ℓ * j) = VG.Proof.MlDsa.Sign.ctV p sk' mu' rnd' (p.ℓ * j) := by
        have := (VG.Proof.MlDsa.Sign.leakT_step ih).1
        simpa [VG.Proof.MlDsa.Sign.signCommit_eq] using this
      simp only [VG.Proof.MlDsa.Sign.contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨by rw [← ect]; exact c1.1, hpass⟩

/-- At an iteration both runs reach: the same `c̃`, the same outcome of
`SampleInBall`, and, if it succeeded, the same outcome of the checks, and
then the same hint. -/
theorem leak_at (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (hb : VG.Proof.MlDsa.Sign.BallF ballF) (h : VG.Proof.MlDsa.Sign.leakV p sk mu rnd = VG.Proof.MlDsa.Sign.leakV p sk' mu' rnd') {t : Nat}
    (ht : t < maxBounds.sign) (hc : ∀ j < t, VG.Proof.MlDsa.Sign.contV p sk mu rnd ballF j = true) :
    VG.Proof.MlDsa.Sign.ctV p sk mu rnd (p.ℓ * t) = VG.Proof.MlDsa.Sign.ctV p sk' mu' rnd' (p.ℓ * t) ∧
      (ballF p.τ (VG.Proof.MlDsa.Sign.ctV p sk mu rnd (p.ℓ * t)) = true →
        (VG.Proof.MlDsa.Sign.passV p sk mu rnd (p.ℓ * t) ↔ VG.Proof.MlDsa.Sign.passV p sk' mu' rnd' (p.ℓ * t)) ∧
        (VG.Proof.MlDsa.Sign.passV p sk mu rnd (p.ℓ * t) → VG.Proof.MlDsa.Sign.hbitsV p sk mu rnd (p.ℓ * t) = VG.Proof.MlDsa.Sign.hbitsV p sk' mu' rnd' (p.ℓ * t))) := by
  obtain ⟨_, ih⟩ := VG.Proof.MlDsa.Sign.leak_iter hp hb h ht hc
  rw [show maxBounds.sign - t = (maxBounds.sign - (t + 1)) + 1 by
    have : maxBounds.sign = 1000 := rfl; omega] at ih
  obtain ⟨hct, _, htag⟩ := VG.Proof.MlDsa.Sign.leakT_step ih
  change VG.Proof.MlDsa.Sign.outTag (VG.Proof.MlDsa.Sign.iterV p sk mu rnd maxBounds (p.ℓ * t)) = VG.Proof.MlDsa.Sign.outTag (VG.Proof.MlDsa.Sign.iterV p sk' mu' rnd' maxBounds (p.ℓ * t)) at htag
  have ect : VG.Proof.MlDsa.Sign.ctV p sk mu rnd (p.ℓ * t) = VG.Proof.MlDsa.Sign.ctV p sk' mu' rnd' (p.ℓ * t) := by simpa [VG.Proof.MlDsa.Sign.signCommit_eq] using hct
  refine ⟨ect, fun hs => ?_⟩
  have hs' : ballF p.τ (VG.Proof.MlDsa.Sign.ctV p sk' mu' rnd' (p.ℓ * t)) = true := by rw [← ect]; exact hs
  have i1 := hb _ _ hs
  have i2 := hb _ _ hs'
  by_cases q1 : VG.Proof.MlDsa.Sign.passV p sk mu rnd (p.ℓ * t) <;> by_cases q2 : VG.Proof.MlDsa.Sign.passV p sk' mu' rnd' (p.ℓ * t)
  · rw [VG.Proof.MlDsa.Sign.iterV_pass hp i1 q1, VG.Proof.MlDsa.Sign.iterV_pass hp i2 q2] at htag
    refine ⟨iff_of_true q1 q2, fun _ => ?_⟩
    simp only [VG.Proof.MlDsa.Sign.outTag, List.cons.injEq, true_and] at htag
    exact htag
  · rw [VG.Proof.MlDsa.Sign.iterV_pass hp i1 q1, VG.Proof.MlDsa.Sign.iterV_rej hp i2 q2] at htag
    simp [VG.Proof.MlDsa.Sign.outTag] at htag
  · rw [VG.Proof.MlDsa.Sign.iterV_rej hp i1 q1, VG.Proof.MlDsa.Sign.iterV_pass hp i2 q2] at htag
    simp [VG.Proof.MlDsa.Sign.outTag] at htag
  · exact ⟨iff_of_false q1 q2, fun h => absurd h q1⟩

/-- Two runs that leak the same run the same number of iterations. -/
theorem itV_eq (hp : VG.Proof.MlDsa.Sign.ParamsOk p) (hb : VG.Proof.MlDsa.Sign.BallF ballF) (h : VG.Proof.MlDsa.Sign.leakV p sk mu rnd = VG.Proof.MlDsa.Sign.leakV p sk' mu' rnd') :
    VG.Proof.MlDsa.Sign.itV p sk mu rnd ballF = VG.Proof.MlDsa.Sign.itV p sk' mu' rnd' ballF :=
  VG.Proof.MlDsa.Sign.nIt_congr (fun M hM ha => (VG.Proof.MlDsa.Sign.leak_iter hp hb h (t := M) (by show M < 1000; omega) ha).1)
    (fun M hM ha => (VG.Proof.MlDsa.Sign.leak_iter hp hb h.symm (t := M) (by show M < 1000; omega) ha).1)

end

end VG.Proof.MlDsa.Sign

end
