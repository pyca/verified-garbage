import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Spec.RsaKeyGen.Contract

/-!
# A candidate: the branches its leak determines

`schedOf`: the branches a candidate takes, as far as it gets: whether it is
too close to `p`; then whether it is obviously composite; then whether
`gcd(c − 1, e) ≠ 1`; then Miller–Rabin's result, with the number of octets
it leaves. Two candidates with the same leak (`candidateLeak`) and as many
random octets take the same branches (`schedOf_eq`).
-/

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Spec.Rsa

/-- The branches a candidate takes. -/
structure Sched where
  close : Bool
  comp : Bool
  gbad : Bool
  mr : Option (Bool × Nat)
  deriving DecidableEq

/-- The branches of the candidate from the first `L` octets of `r`, for the
exponent `e` and the other prime `p`. -/
def schedOf (L e : Nat) (p : Option Nat) (r : Rand) : Sched :=
  let c := candidate (8 * L) (os2ip (r.take L))
  if tooClose (8 * L) p c then ⟨true, false, false, none⟩
  else if obviouslyComposite (8 * L) c then ⟨false, true, false, none⟩
  else if !(Nat.gcd (c - 1) e == 1) then ⟨false, false, true, none⟩
  else ⟨false, false, false, (primalityTest c (r.drop L)).map fun x => (x.1, x.2.length)⟩

/-- A loop whose steps never lengthen the octets left. -/
theorem loop_rest {σ α : Type} {step : σ → Rand → Option ((α ⊕ σ) × Rand)}
    (hstep : ∀ s r x r', step s r = some (x, r') → r'.length ≤ r.length) :
    ∀ s r a r', loop step s r = some (a, r') → r'.length ≤ r.length := by
  intro s r
  induction r using (measure List.length).wf.induction generalizing s with
  | h r ih =>
    intro a r' h
    rw [loop] at h
    split at h
    · cases h
    · cases h
      exact hstep _ _ _ _ (by assumption)
    · split at h
      · rename_i hlt
        exact Nat.le_trans (ih _ hlt _ _ _ h) (Nat.le_of_lt hlt)
      · cases h

theorem draw_rest {n : Nat} {r : Rand} {x : Nat} {r' : Rand} (h : draw n r = some (x, r')) :
    r'.length ≤ r.length := by
  unfold draw at h
  simp only at h
  split at h
  · cases h; simp
  · cases h

/-- A step of Miller–Rabin's loop leaves at most the octets it was given. -/
theorem mrStep_rest {c ch a m : Nat} : ∀ (s : Nat × Nat) (r : Rand) x r', mrStep c ch a m s r = some (x, r') →
    r'.length ≤ r.length := by
  intro s r x r' hs
  obtain ⟨i, u⟩ := s
  unfold mrStep at hs
  simp only at hs
  by_cases hg : i ≤ blindedChecks ∨ u < ch
  · rw [ite_t hg] at hs
    rcases hd : draw (witnessBytes c) r with _ | ⟨y, r₁⟩
    · simp [hd] at hs
    · simp only [hd, Option.bind_eq_bind, Option.bind_some] at hs
      have := draw_rest hd
      by_cases hm : mrIteration c a m (witness (c - 1) y).1 = true <;>
        simp only [hm, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true] at hs <;>
        (obtain ⟨-, rfl⟩ := hs; exact this)
  · rw [ite_f hg] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs; exact Nat.le_refl _

/-- Miller–Rabin's loop from a state that draws, at the offset `used`: what
it leaves is after the next witness. -/
theorem mrLoop_rest {c ch a m L : Nat} {r : Rand} {i uni used : Nat} (hgo : i ≤ blindedChecks ∨ uni < ch)
    (hwb : witnessBytes c = L) (hL : 0 < L) {b : Bool} {rest : Rand}
    (h : loop (mrStep c ch a m) (i, uni) (r.drop used) = some (b, rest)) : rest.length + (used + L) ≤ r.length := by
  rw [mrLoop_step c ch a m L r i uni used hgo hwb hL] at h
  split at h
  · split at h
    · have := loop_rest mrStep_rest _ _ _ _ h
      simp only [List.length_drop] at this
      omega
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [List.length_drop]; omega
  · cases h

/-- Miller–Rabin leaves at most the octets it was given. -/
theorem primalityTest_rest {c : Nat} {r : Rand} {b : Bool} {rest : Rand} (h : primalityTest c r = some (b, rest)) :
    rest.length ≤ r.length := by
  unfold primalityTest at h
  split at h
  · cases h; exact Nat.le_refl _
  split at h
  · cases h; exact Nat.le_refl _
  split at h
  · cases h; exact Nat.le_refl _
  refine loop_rest (fun s r x r' hs => ?_) _ _ _ _ h
  obtain ⟨i, u⟩ := s
  unfold mrStep at hs
  simp only at hs
  by_cases hg : i ≤ blindedChecks ∨ u < checksForSize (bitLength c)
  · rw [ite_t hg] at hs
    rcases hd : draw (witnessBytes c) r with _ | ⟨y, r₁⟩
    · simp [hd] at hs
    · simp only [hd, Option.bind_eq_bind, Option.bind_some] at hs
      have := draw_rest hd
      by_cases hm : mrIteration c (splitTwos (c - 1)).1 (splitTwos (c - 1)).2 (witness (c - 1) y).1 = true <;>
        simp only [hm, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true] at hs <;>
        (obtain ⟨-, rfl⟩ := hs; exact this)
  · rw [ite_f hg] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs; exact Nat.le_refl _

theorem map_toNat_inj : ∀ {a b : List Byte}, a.map (·.toNat) = b.map (·.toNat) → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]

theorem take_eq_of_map {r₁ r₂ : List Byte} {u₁ u₂ : Nat} (h₁ : u₁ ≤ r₁.length) (h₂ : u₂ ≤ r₂.length)
    (h : (r₁.take u₁).map (·.toNat) = (r₂.take u₂).map (·.toNat)) : u₁ = u₂ ∧ r₁.take u₁ = r₂.take u₂ := by
  have e := map_toNat_inj h
  have := congrArg List.length e
  simp only [List.length_take] at this
  exact ⟨by omega, e⟩

theorem take_take_of_le {r : List Byte} {a b : Nat} (h : a ≤ b) : (r.take b).take a = r.take a := by
  rw [List.take_take, Nat.min_eq_left h]

/-- What a candidate leaks, from what became of it. -/
def leakOf (r : Rand) : Option (Candidate × Rand) → List Nat
  | none => [0]
  | some (.prime _, rest) => [1, r.length - rest.length]
  | some (.close, _) => [2]
  | some (.rejected, rest) => 3 :: (r.take (r.length - rest.length)).map (·.toNat)

theorem candidateLeak_eq (L : Nat) (eB pB r : List Byte) :
    candidateLeak L eB pB r = leakOf r (candidateOp L eB pB r) := by
  unfold candidateLeak
  rcases candidateOp L eB pB r with _ | ⟨_ | _ | _, rest⟩ <;> rfl

/-- Candidates with the same leak and as many random octets (enough for the
candidate) take the same branches. -/
theorem schedOf_eq {L e : Nat} {p₁ p₂ : Option Nat} {r₁ r₂ : List Byte} (hL : 0 < L) (hr : r₁.length = r₂.length)
    (hk : L ≤ r₁.length)
    (h : leakOf r₁ (candidateStep (8 * L) e p₁ r₁) = leakOf r₂ (candidateStep (8 * L) e p₂ r₂)) :
    schedOf L e p₁ r₁ = schedOf L e p₂ r₂ := by
  rw [candidateStep_eq L _ _ _ hL, candidateStep_eq L _ _ _ hL, ite_t hk, ite_t (hr ▸ hk)] at h
  have hs : ∀ r : Rand, seg r 0 L = r.take L := fun r => by simp [seg]
  rw [hs, hs] at h
  unfold schedOf
  generalize hc₁ : candidate (8 * L) (os2ip (r₁.take L)) = c₁ at h ⊢
  generalize hc₂ : candidate (8 * L) (os2ip (r₂.take L)) = c₂ at h ⊢
  have hd₁ : r₁.length - (r₁.drop L).length = L := by simp; omega
  have hd₂ : r₂.length - (r₂.drop L).length = L := by simp; omega
  -- What each run leaks and takes.
  have cls : ∀ (c : Nat) (p : Option Nat) (r : Rand), r.length - (r.drop L).length = L →
      (tooClose (8 * L) p c = true ∧ leakOf r (afterDraw (8 * L) e p c (r.drop L)) = [2]) ∨
      (tooClose (8 * L) p c = false ∧ (obviouslyComposite (8 * L) c = true ∨ (!(Nat.gcd (c - 1) e == 1)) = true) ∧
        leakOf r (afterDraw (8 * L) e p c (r.drop L)) = 3 :: (r.take L).map (·.toNat)) ∨
      (tooClose (8 * L) p c = false ∧ obviouslyComposite (8 * L) c = false ∧ (!(Nat.gcd (c - 1) e == 1)) = false ∧
        leakOf r (afterDraw (8 * L) e p c (r.drop L)) = leakOf r ((primalityTest c (r.drop L)).map fun pr =>
          (if pr.1 then .prime c else .rejected, pr.2))) := by
    intro c p r hd
    unfold afterDraw
    by_cases t : tooClose (8 * L) p c
    · exact Or.inl ⟨t, by simp [t, leakOf]⟩
    · rw [ite_f t]
      by_cases g : (!obviouslyComposite (8 * L) c && Nat.gcd (c - 1) e == 1) = true
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at g
        refine Or.inr (Or.inr ⟨Bool.eq_false_iff.mpr t, g.1, by simp [g.2], ?_⟩)
        rw [ite_t (by simp [g.1, g.2])]
      · refine Or.inr (Or.inl ⟨Bool.eq_false_iff.mpr t, ?_, ?_⟩)
        · simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at g
          cases ho : obviouslyComposite (8 * L) c
          · simp only [Bool.not_eq_true']
            have := g ho; simpa using this
          · exact Or.inl rfl
        · rw [ite_f g]; simp only [leakOf, hd]
  have hrest : ∀ (c : Nat) (r : Rand) b rest, primalityTest c (r.drop L) = some (b, rest) → rest.length ≤ r.length :=
    fun c r b rest hp => Nat.le_trans (primalityTest_rest hp) (by simp)
  -- Equal candidates from equal first octets.
  have same : r₁.take L = r₂.take L → c₁ = c₂ := fun e => by rw [← hc₁, ← hc₂, e]
  rcases cls c₁ p₁ r₁ hd₁ with ⟨t₁, l₁⟩ | ⟨t₁, g₁, l₁⟩ | ⟨t₁, o₁, g₁, l₁⟩ <;>
  rcases cls c₂ p₂ r₂ hd₂ with ⟨t₂, l₂⟩ | ⟨t₂, g₂, l₂⟩ | ⟨t₂, o₂, g₂, l₂⟩ <;>
  rw [l₁, l₂] at h
  · simp [t₁, t₂]
  · simp at h
  · rcases hp : primalityTest c₂ (r₂.drop L) with _ | ⟨_ | _, rest⟩ <;> simp [hp, leakOf] at h
  · simp at h
  · obtain rfl := same (map_toNat_inj (List.cons.inj h).2)
    dsimp only
    rw [t₁, t₂]
    rcases g₁ with g | g <;> simp [g]
  · rcases hp : primalityTest c₂ (r₂.drop L) with _ | ⟨_ | _, rest⟩
    · simp [hp, leakOf] at h
    · simp only [hp, leakOf, Option.map_some, Bool.false_eq_true, ↓reduceIte, List.cons.injEq] at h
      obtain ⟨hu, e⟩ := take_eq_of_map hk (by have := hrest _ _ _ _ hp; omega) h.2
      rw [← hu] at e
      obtain rfl := same e
      rcases g₁ with g₁ | g₁
      · rw [g₁] at o₂; cases o₂
      · rw [g₁] at g₂; cases g₂
    · simp [hp, leakOf] at h
  · rcases hp : primalityTest c₁ (r₁.drop L) with _ | ⟨_ | _, rest⟩ <;> simp [hp, leakOf] at h
  · rcases hp : primalityTest c₁ (r₁.drop L) with _ | ⟨_ | _, rest⟩
    · simp [hp, leakOf] at h
    · simp only [hp, leakOf, Option.map_some, Bool.false_eq_true, ↓reduceIte, List.cons.injEq] at h
      obtain ⟨hu, e⟩ := take_eq_of_map (by have := hrest _ _ _ _ hp; omega) (by omega) h.2
      rw [hu] at e
      obtain rfl := same e
      rcases g₂ with g₂ | g₂
      · rw [g₂] at o₁; cases o₁
      · rw [g₂] at g₁; cases g₁
    · simp [hp, leakOf] at h
  · dsimp only
    rw [t₁, t₂, o₁, o₂, g₁, g₂]
    simp only [Bool.false_eq_true, ↓reduceIte, Sched.mk.injEq, true_and]
    rcases hp₁ : primalityTest c₁ (r₁.drop L) with _ | ⟨b₁, rest₁⟩
    · rcases hp₂ : primalityTest c₂ (r₂.drop L) with _ | ⟨b₂, rest₂⟩
      · rfl
      · rw [hp₁, hp₂] at h; cases b₂ <;> simp [leakOf] at h
    · rcases hp₂ : primalityTest c₂ (r₂.drop L) with _ | ⟨b₂, rest₂⟩
      · rw [hp₁, hp₂] at h; cases b₁ <;> simp [leakOf] at h
      · rw [hp₁, hp₂] at h
        have l₁ := hrest _ _ _ _ hp₁
        have l₂ := hrest _ _ _ _ hp₂
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        cases b₁ <;> cases b₂
        · simp only [leakOf, Option.map_some, Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and] at h ⊢
          obtain ⟨hu, -⟩ := take_eq_of_map (by omega) (by omega) h
          omega
        · simp [leakOf] at h
        · simp [leakOf] at h
        · simp only [leakOf, Option.map_some, ↓reduceIte, List.cons.injEq, true_and, and_true] at h ⊢
          omega

/-! ## Miller–Rabin's iterations -/

/-- The shape of a result: what became of it, and the octets it left. -/
def shapeOf (res : Option (Bool × Rand)) : Option (Bool × Nat) := res.map fun x => (x.1, x.2.length)

/-- The witnesses left to draw at offset `u`, of `L` octets each, for the
shape `S` of the result, with `rl` octets in all. -/
def itersOf (L rl : Nat) (S : Option (Bool × Nat)) (u : Nat) : Nat :=
  match S with
  | none => (rl - u) / L + 1
  | some (_, n) => (rl - n - u) / L

/-- Whether the witness at offset `u` passes, from the shape of the result. -/
def passS (L rl : Nat) (S : Option (Bool × Nat)) (u : Nat) : Bool := !(S == some (false, rl - u - L))

/-- The witness at offset `used` passes iff the result is not that it failed
there. -/
theorem mr_pass {c ch a m L : Nat} {r : Rand} {i uni used : Nat} (hgo : i ≤ blindedChecks ∨ uni < ch)
    (hwb : witnessBytes c = L) (hL : 0 < L) (hav : used + L ≤ r.length) :
    passS L r.length (shapeOf (loop (mrStep c ch a m) (i, uni) (r.drop used))) used =
      mrIteration c a m (witness (c - 1) (os2ip (seg r used L))).1 := by
  rw [mrLoop_step c ch a m L r i uni used hgo hwb hL, ite_t hav]
  by_cases hm : mrIteration c a m (witness (c - 1) (os2ip (seg r used L))).1 = true
  · rw [ite_t hm, hm]
    unfold passS
    generalize hn : i + 1 = i' at *
    generalize hu : uni + (if (witness (c - 1) (os2ip (seg r used L))).2 = true then 1 else 0) = u' at *
    by_cases hg : i' ≤ blindedChecks ∨ u' < ch
    · rcases h : loop (mrStep c ch a m) (i', u') (r.drop (used + L)) with _ | ⟨b, rest⟩
      · rfl
      · have := mrLoop_rest hg hwb hL h
        simp [shapeOf]
        intro _; omega
    · rw [mrLoop_done c ch a m _ i' u' hg]
      simp [shapeOf]
  · rw [ite_f hm]
    simp only [Bool.not_eq_true] at hm
    rw [hm]
    simp [passS, shapeOf]
    omega

/-- An iteration that goes on, to the state `(i, uni)` that draws at offset
`u`: one more iteration than from there, and at least one from there. -/
theorem iters_cont {c ch a m L : Nat} {r : Rand} {i uni u : Nat} (hgo : i ≤ blindedChecks ∨ uni < ch)
    (hwb : witnessBytes c = L) (hL : 0 < L) (hu : L ≤ u) (hul : u ≤ r.length) :
    itersOf L r.length (shapeOf (loop (mrStep c ch a m) (i, uni) (r.drop u))) (u - L) =
      itersOf L r.length (shapeOf (loop (mrStep c ch a m) (i, uni) (r.drop u))) u + 1 ∧
    1 ≤ itersOf L r.length (shapeOf (loop (mrStep c ch a m) (i, uni) (r.drop u))) u := by
  rcases h : loop (mrStep c ch a m) (i, uni) (r.drop u) with _ | ⟨b, rest⟩
  · simp only [shapeOf, Option.map_none, itersOf]
    refine ⟨?_, Nat.le_add_left 1 _⟩
    rw [show r.length - (u - L) = r.length - u + L by omega, Nat.add_div_right _ hL]
  · have := mrLoop_rest hgo hwb hL h
    simp only [shapeOf, Option.map_some, itersOf]
    refine ⟨?_, ?_⟩
    · rw [show r.length - rest.length - (u - L) = r.length - rest.length - u + L by omega, Nat.add_div_right _ hL]
    · exact (Nat.le_div_iff_mul_le hL).mpr (by omega)

/-- The last iteration: one left. -/
theorem iters_end_none {L rl u : Nat} (hL : 0 < L) (h : rl < u + L) : itersOf L rl none u = 1 := by
  simp only [itersOf, Nat.add_eq_right, Nat.div_eq_zero_iff]; omega

theorem iters_end_some {L rl u : Nat} {b : Bool} {n : Nat} (hL : 0 < L) (h : n + (u + L) = rl) :
    itersOf L rl (some (b, n)) u = 1 := by
  simp only [itersOf]; rw [show rl - n - u = L by omega, Nat.div_self hL]

end VG.Proof.RsaKeyGen
