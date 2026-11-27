module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Loads
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Instr
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint1
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin3
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `RsaKeyGen.Arm.Cand.Fin4`, which the modules that import this one used -/

section

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
    (by have := pre.k1; omega_using [this])
  rw [rB_length, ite_t hL, ← xB_seg hL] at this
  exact this

theorem res_none (pre : In P σ) (hl : P.rl < P.L) : res P σ = none := by
  have := VG.Proof.RsaKeyGen.candidateStep_eq P.L P.e (Spec.RsaKeyGen.otherPrime (pB P σ)) (rB P σ)
    (by have := pre.k1; omega_using [hl])
  rw [rB_length, ite_f (by omega_using [hl])] at this
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

end

end

/-! # A candidate on ARMv7: whether `rand` holds a candidate

`lenCheck_vp`: Z iff `rand_len < out_len`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : CP}

theorem lenCheck_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bk P σ s) (.block lenCheck)
      (fun σ s => (E σ ∧ Bk P σ s) ∧ s.z = decide (P.rl < P.L)) := by
  rw [lenCheck_eq]
  refine VP.block_append (G := fun σ s => (E σ ∧ Bk P σ s) ∧ s.gpr .r1 = BitVec.ofNat 32 P.rl ∧
    s.gpr .r2 = BitVec.ofNat 32 P.L) ?_ ?_
  · show VP _ (.block ([(Reg.r1, aoRl), (Reg.r2, foL)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.sp, h₁.2.pre.sp, h₂.2.sp, h₂.2.pre.sp]
    · refine h.ldrSp (o := aoRl) (by decide) fun s1 u1 => ?_
      refine (h.of_upd u1).ldrSp (o := foL) (by decide) fun t u2 => WP.block_nil ?_
      exact ⟨⟨e, (h.of_upd u1).of_upd u2⟩, by rw [u2.other _ (by decide), u1.gpr, h.pre.aRl],
        by rw [u2.gpr, h.pre.wL]⟩
  · refine VP.taint [.r1, .r2] carryTail_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h⟩, r1, r2⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]
    have pre := h.pre
    have hr : P.rl < 2 ^ 32 := pre.rlt
    have hl : P.L < 2 ^ 32 := by have := pre.k2; omega_using [this]
    refine carry_ok fun s1 r1' m1 v1 => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil
      ⟨⟨e, (h.of_rest r1' m1).of_rest (f.rest []) f.mem⟩, ?_⟩
    rw [z, v1, r1, r2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hl]
    by_cases hc : P.L ≤ P.rl
    · simp [hc]
    · simp [hc]; omega_using [hc]

end

end VG.Proof.RsaKeyGen.Arm.Cand
