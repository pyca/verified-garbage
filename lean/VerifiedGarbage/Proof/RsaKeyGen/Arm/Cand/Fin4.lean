module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin3
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the contract's result by branch

The status, `out` and `used` of the result (`stR`, `outR`, `usedR`) for
each branch the candidate takes, which the branches `P.sch` give
(`sched_close`, …).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Impl.RsaKeyGen.Arm.Candidate
open VG.Proof.RsaKeyGen (ite_t ite_f afterDraw)

/-- The status, `out` and `used` of the result. -/
def stR (P : CP) (σ : State) : Nat := Spec.RsaKeyGen.candidateStatus (res P σ)
def outR (P : CP) (σ : State) : List Byte :=
  match res P σ with
  | some (.prime c, _) => Spec.Rsa.i2osp c P.L
  | _ => List.replicate P.L 0
def usedR (P : CP) (σ : State) : Nat :=
  match res P σ with
  | some (_, rest) => P.rl - rest.length
  | none => 0

section
variable {P : CP} {σ : State}

theorem res_eq (pre : In P σ) (hL : P.L ≤ P.rl) :
    res P σ = afterDraw (8 * P.L) P.e (Spec.RsaKeyGen.otherPrime (pB P σ)) (cv P σ) ((rB P σ).drop P.L) := by
  have := VG.Proof.RsaKeyGen.candidateStep_eq P.L P.e (Spec.RsaKeyGen.otherPrime (pB P σ)) (rB P σ)
    (by have := pre.k1; omega)
  rw [rB_length, ite_t hL, ← xB_seg hL] at this
  exact this

theorem res_none (pre : In P σ) (hl : P.rl < P.L) : res P σ = none := by
  have := VG.Proof.RsaKeyGen.candidateStep_eq P.L P.e (Spec.RsaKeyGen.otherPrime (pB P σ)) (rB P σ)
    (by have := pre.k1; omega)
  rw [rB_length, ite_f (by omega)] at this
  exact this

theorem res_close (pre : In P σ) (hL : P.L ≤ P.rl) (h : clv P σ = true) :
    res P σ = some (.close, (rB P σ).drop P.L) := by
  have h' : Spec.RsaKeyGen.tooClose (8 * P.L) (Spec.RsaKeyGen.otherPrime (pB P σ)) (cv P σ) = true := h
  rw [res_eq pre hL]
  unfold afterDraw
  rw [ite_t h']

theorem res_rej (pre : In P σ) (hL : P.L ≤ P.rl) (hcl : clv P σ = false)
    (h : (!compv P σ && gv P σ) = false) : res P σ = some (.rejected, (rB P σ).drop P.L) := by
  have h1 : Spec.RsaKeyGen.tooClose (8 * P.L) (Spec.RsaKeyGen.otherPrime (pB P σ)) (cv P σ) = false := hcl
  have h2 : (!Spec.RsaKeyGen.obviouslyComposite (8 * P.L) (cv P σ) && Nat.gcd (cv P σ - 1) P.e == 1) = false := h
  rw [res_eq pre hL]
  unfold afterDraw
  rw [ite_f (by rw [h1]; decide), ite_f (by rw [h2]; decide)]

theorem res_mr (pre : In P σ) (hm : EM P σ) :
    stR P σ = statQ P σ ∧ outR P σ = outM P σ ∧ usedR P σ = usedM P σ := by
  obtain ⟨hL, hcl, hco, hg⟩ := hm
  have h1 : Spec.RsaKeyGen.tooClose (8 * P.L) (Spec.RsaKeyGen.otherPrime (pB P σ)) (cv P σ) = false := hcl
  have h2 : (!Spec.RsaKeyGen.obviouslyComposite (8 * P.L) (cv P σ) && Nat.gcd (cv P σ - 1) P.e == 1) = true := by
    have a : Spec.RsaKeyGen.obviouslyComposite (8 * P.L) (cv P σ) = false := hco
    have b : (Nat.gcd (cv P σ - 1) P.e == 1) = true := hg
    rw [a, b]; rfl
  have e : res P σ = (resP P σ).map fun pr => (if pr.1 then .prime (cv P σ) else .rejected, pr.2) := by
    rw [res_eq pre hL]
    unfold afterDraw
    rw [ite_f (by rw [h1]; decide), ite_t h2]
    rfl
  unfold stR outR usedR outM usedM
  rw [e]
  unfold statQ usedQ
  rcases resP P σ with _ | ⟨_ | _, rest⟩ <;> simp [Spec.RsaKeyGen.candidateStatus]

theorem sched_eq (pre : In P σ) (hL : P.L ≤ P.rl) :
    P.sch = if clv P σ then ⟨true, false, false, none⟩ else if compv P σ then ⟨false, true, false, none⟩
      else if !gv P σ then ⟨false, false, true, none⟩
      else ⟨false, false, false, (resP P σ).map fun x => (x.1, x.2.length)⟩ := by
  rw [← pre.sch hL]
  unfold VG.Proof.RsaKeyGen.schedOf
  rw [take_rB hL]
  rfl

theorem sched_close (pre : In P σ) (hL : P.L ≤ P.rl) : P.sch.close = clv P σ := by
  rw [sched_eq pre hL]
  cases clv P σ <;> cases compv P σ <;> cases gv P σ <;> rfl

theorem sched_comp (pre : In P σ) (hL : P.L ≤ P.rl) (hcl : clv P σ = false) : P.sch.comp = compv P σ := by
  rw [sched_eq pre hL, hcl]
  cases compv P σ <;> cases gv P σ <;> rfl

theorem sched_gbad (pre : In P σ) (hL : P.L ≤ P.rl) (hcl : clv P σ = false) (hco : compv P σ = false) :
    P.sch.gbad = !gv P σ := by
  rw [sched_eq pre hL, hcl, hco]
  cases gv P σ <;> rfl

end

end VG.Proof.RsaKeyGen.Arm.Cand
