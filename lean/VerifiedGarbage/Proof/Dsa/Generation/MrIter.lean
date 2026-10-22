module

public import VerifiedGarbage.Proof.RsaKeyGen.MrIter
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec

/-!
# DSA's probable-prime test: Miller–Rabin, witness by witness

As `Proof/RsaKeyGen/MrIter.lean` for RSA's candidate, but with the witnesses
drawn from the start of the tape, the `k`-th at offset `D k`: DSA's test
reads no candidate from the tape. `dmrS c D r k`: the counts `(i, uniform)`
of the loop after `k` witnesses passed. `DMrAt … k n`: the loop from the
start is the loop from there, it draws again, and `n + 1` iterations of an
implementation that also counts the last, failing, draw are left
(`itersOf`). A witness that is drawn and passes leads to `DMrAt … (k + 1)
(n − 1)` if more are needed (`dmrAt_next`); otherwise the loop's result is
known and `n = 0` (`dmrAt_done`, `dmrAt_fail`, `dmrAt_short`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Generation

open VG.Spec.RsaKeyGen VG.Spec.Rsa
open VG.Proof.RsaKeyGen (seg goS itersOf shapeOf mrLoop_step mrLoop_done iters_cont ite_t ite_f)

/-- The witness drawn at offset `u`. -/
def dwit (c D : Nat) (r : Rand) (u : Nat) : Nat × Bool := witness (c - 1) (os2ip (seg r u D))

/-- The counts after `k` witnesses passed. -/
def dmrS (c D : Nat) (r : Rand) : Nat → Nat × Nat
  | 0 => (1, 0)
  | k + 1 => ((dmrS c D r k).1 + 1, (dmrS c D r k).2 + if (dwit c D r (D * k)).2 then 1 else 0)

/-- The loop's result from the start of the tape. -/
abbrev dres (c ch a m : Nat) (r : Rand) : Option (Bool × Rand) := loop (mrStep c ch a m) (1, 0) r

/-- After `k` witnesses passed, with `n + 1` iterations left. -/
structure DMrAt (c ch a m D : Nat) (r : Rand) (k n : Nat) : Prop where
  loop : dres c ch a m r = loop (mrStep c ch a m) (dmrS c D r k) (r.drop (D * k))
  go : goS ch (dmrS c D r k)
  iters : itersOf D r.length (shapeOf (dres c ch a m r)) (D * k) = n + 1
  used : D * k ≤ r.length

section
variable {c ch a m D : Nat} {r : Rand} {k n : Nat}

/-- The witness passes and more are needed. -/
theorem dmrAt_next (h : DMrAt c ch a m D r k n) (hwb : witnessBytes c = D) (hD : 0 < D)
    (hav : D * k + D ≤ r.length) (hp : mrIteration c a m (dwit c D r (D * k)).1 = true)
    (hg : goS ch (dmrS c D r (k + 1))) : 0 < n ∧ DMrAt c ch a m D r (k + 1) (n - 1) := by
  have e := mrLoop_step c ch a m D r (dmrS c D r k).1 (dmrS c D r k).2 (D * k) h.go hwb hD
  rw [ite_t hav] at e
  unfold dwit at hp
  rw [ite_t hp] at e
  have hk : D * k + D = D * (k + 1) := (Nat.mul_succ D k).symm
  rw [hk] at e
  have l1 : dres c ch a m r = loop (mrStep c ch a m) (dmrS c D r (k + 1)) (r.drop (D * (k + 1))) := by
    rw [h.loop, e]; rfl
  have ic := iters_cont (c := c) (ch := ch) (a := a) (m := m) (r := r) (i := (dmrS c D r (k + 1)).1)
    (uni := (dmrS c D r (k + 1)).2) (u := D * (k + 1)) hg hwb hD (by rw [Nat.mul_succ]; omega) (by omega)
  rw [← l1, show D * (k + 1) - D = D * k by rw [Nat.mul_succ]; omega, h.iters] at ic
  exact ⟨by omega, ⟨l1, hg, by omega, by omega⟩⟩

/-- The witness passes and no more are needed: `c` is probably prime. -/
theorem dmrAt_done (h : DMrAt c ch a m D r k n) (hwb : witnessBytes c = D) (hD : 0 < D)
    (hav : D * k + D ≤ r.length) (hp : mrIteration c a m (dwit c D r (D * k)).1 = true)
    (hg : ¬ goS ch (dmrS c D r (k + 1))) :
    n = 0 ∧ dres c ch a m r = some (true, r.drop (D * k + D)) := by
  have e := mrLoop_step c ch a m D r (dmrS c D r k).1 (dmrS c D r k).2 (D * k) h.go hwb hD
  rw [ite_t hav] at e
  unfold dwit at hp
  rw [ite_t hp] at e
  have d := mrLoop_done c ch a m (r.drop (D * k + D)) (dmrS c D r (k + 1)).1 (dmrS c D r (k + 1)).2 hg
  have l1 : dres c ch a m r = some (true, r.drop (D * k + D)) := by
    rw [h.loop, e]; exact d
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_some, itersOf, List.length_drop] at this
  rw [show r.length - (r.length - (D * k + D)) - D * k = D by omega, Nat.div_self hD] at this
  omega

/-- The witness fails: `c` is composite. -/
theorem dmrAt_fail (h : DMrAt c ch a m D r k n) (hwb : witnessBytes c = D) (hD : 0 < D)
    (hav : D * k + D ≤ r.length) (hp : mrIteration c a m (dwit c D r (D * k)).1 = false) :
    n = 0 ∧ dres c ch a m r = some (false, r.drop (D * k + D)) := by
  have e := mrLoop_step c ch a m D r (dmrS c D r k).1 (dmrS c D r k).2 (D * k) h.go hwb hD
  rw [ite_t hav] at e
  unfold dwit at hp
  rw [ite_f (by simp [hp])] at e
  have l1 : dres c ch a m r = some (false, r.drop (D * k + D)) := by rw [h.loop, e]
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_some, itersOf, List.length_drop] at this
  rw [show r.length - (r.length - (D * k + D)) - D * k = D by omega, Nat.div_self hD] at this
  omega

/-- Too few octets left for the witness. -/
theorem dmrAt_short (h : DMrAt c ch a m D r k n) (hwb : witnessBytes c = D) (hD : 0 < D)
    (hav : ¬ D * k + D ≤ r.length) : n = 0 ∧ dres c ch a m r = none := by
  have e := mrLoop_step c ch a m D r (dmrS c D r k).1 (dmrS c D r k).2 (D * k) h.go hwb hD
  rw [ite_f hav] at e
  have l1 : dres c ch a m r = none := by rw [h.loop, e]
  refine ⟨?_, l1⟩
  have := h.iters
  rw [l1] at this
  simp only [shapeOf, Option.map_none, itersOf] at this
  rw [Nat.div_eq_of_lt (by omega)] at this
  omega

/-- The iterations from the start: at least one, the first draw's. -/
theorem iters_start (hwb : witnessBytes c = D) (hD : 0 < D) :
    1 ≤ itersOf D r.length (shapeOf (dres c ch a m r)) 0 := by
  have hg : goS ch ((1 : Nat), (0 : Nat)) := .inl (by simp [blindedChecks])
  let r' : Rand := List.replicate D 0 ++ r
  have hd : r'.drop D = r := by simp [r']
  have hl : r'.length = r.length + D := by simp [r', Nat.add_comm]
  have := (iters_cont (c := c) (ch := ch) (a := a) (m := m) (r := r') (i := 1) (uni := 0) (u := D) hg hwb hD
    (Nat.le_refl _) (by omega)).2
  rw [hd, hl] at this
  unfold dres
  generalize loop (mrStep c ch a m) (1, 0) r = x at this ⊢
  rcases x with _ | ⟨b, rest⟩
  · simp only [shapeOf, Option.map_none, itersOf]; exact Nat.le_add_left 1 _
  · simp only [shapeOf, Option.map_some, itersOf] at this ⊢
    rw [show r.length + D - rest.length - D = r.length - rest.length - 0 by omega] at this
    exact this

/-- The start. -/
theorem dmrAt_zero (hwb : witnessBytes c = D) (hD : 0 < D) :
    DMrAt c ch a m D r 0 (itersOf D r.length (shapeOf (dres c ch a m r)) 0 - 1) := by
  have hg : goS ch (dmrS c D r 0) := .inl (by simp [dmrS, blindedChecks])
  refine ⟨by simp [dmrS], hg, ?_, by simp⟩
  have := iters_start (ch := ch) (a := a) (m := m) (r := r) hwb hD
  rw [Nat.mul_zero]
  omega

end

end VG.Proof.Dsa.Generation
