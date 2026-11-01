module
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Out2

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Out3
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

/-! # An RSA key on ARMv7: the body (`body_vp`)

From the start of the body (`Bk`): the status of `resv` returned, and the
outputs it gives (`outE`), constant time with the status public.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

/-- Output `i` of the result. -/
def outE (P : KP) (σ : State) (i : Nat) : List Byte :=
  match resv P σ with
  | .inl (.ok ys) => ys.getD i []
  | _ => List.replicate (oLen P i) 0

/-- The end of the body. -/
def Res (P : KP) (σ s : State) : Prop :=
  Bo P σ s ∧ (s.gpr .r0).toNat = Spec.RsaKeyGen.keyStatus (resv P σ) ∧
    ∀ i < 7, Spec.Rsa.bytesAt s.mem (State.addr (oPtr P i)) (oLen P i) = outE P σ i

theorem i2osp_mod (x L : Nat) : Spec.Rsa.i2osp (x % 2 ^ (8 * L)) L = Spec.Rsa.i2osp x L := by
  unfold Spec.Rsa.i2osp
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have e : 2 ^ (8 * L) = 256 ^ (L - 1 - i) * 256 ^ (i + 1) := by
    rw [← Nat.pow_add, show L - 1 - i + (i + 1) = L by omega, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  rw [e, Nat.mod_mul_right_div_self]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by rw [Nat.pow_succ]; exact Nat.dvd_mul_left 256 _)

section
variable {P : KP}

theorem smv_eq [VG.Proof.Rsa.Arm.Keys.InvLaw] {σ : State} (pre : In P σ) : smv P σ = decide (P.st = 2) := by
  have := pre.st
  rw [res_spec pre] at this
  unfold resv at this
  rw [← this]
  unfold smv
  cases h : (okv P σ && decide (dv P σ ≤ 2 ^ (8 * P.K)))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  · rfl

theorem smv_of {σ s : State} (z : s.z = decide (b2n (smv P σ) = 1)) (t : isa.eval .eq s = some true) :
    smv P σ = true := by
  rw [isa_eq] at t; cases h : smv P σ <;> simp_all [b2n]

theorem smv_of' {σ s : State} (z : s.z = decide (b2n (smv P σ) = 1)) (t : isa.eval .eq s = some false) :
    smv P σ = false := by
  rw [isa_eq] at t; cases h : smv P σ <;> simp_all [b2n]

theorem resv_small {σ : State} (h : smv P σ = true) : resv P σ = .inr () := by
  unfold resv; unfold smv at h; rw [ite_eq_left h]

theorem resv_key {σ : State} (h : smv P σ = false) :
    resv P σ = if maskv P σ = true then .inl (.ok (outv P σ)) else .inl (.error .internal) := by
  unfold resv; unfold smv at h; rw [ite_eq_right (by rw [h]; decide)]

/-- An output written from its array is the result's. -/
theorem oExp_eq {σ : State} (h : smv P σ = false) (i : Nat) (hi : i < 7) : oExp P σ i = outE P σ i := by
  unfold oExp outE
  rw [resv_key h]
  cases hm : maskv P σ
  · rfl
  · simp only [↓reduceIte]
    rw [i2osp_mod]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [AK, A5, AS3, upd, ↓reduceIte, AH_P, AH_Q, oArr, oLen, outv,
      List.getD_cons_zero, List.getD_cons_succ]

/-- The body after the entry. -/
theorem body_vp [VG.Proof.Rsa.Arm.Keys.InvLaw] : VP (fun σ s => In P σ ∧ Bk P σ s) body (Res P) := by
  simp only [body, seqs]
  refine loads_vp.seq (primes_vp.seq (lcm_vp.seq (eFlags_vp.seq (dPart_vp.seq
    ((small_vp (E := In P) fun _ e => e).seq ?_)))))
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · rw [isa_eq, isa_eq, h₁.2, h₂.2, smv_eq h₁.1.1, smv_eq h₂.1.1]
  · refine (zeros_vp (E := fun σ => In P σ ∧ smv P σ = true)).mono
      (fun σ s ⟨⟨h, z⟩, t⟩ => ⟨⟨h.1, smv_of z t⟩, h.2.1.bo, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun σ s ⟨⟨⟨_, sm⟩, bo, outs⟩, r0⟩ => ⟨bo, ?_, fun i hi => ?_⟩
    · rw [r0, resv_small sm]; rfl
    · rw [outs i hi]; unfold outE; rw [resv_small sm]
  · simp only [keyPart, seqs]
    refine VP.mono (F := G5 P (fun σ => In P σ ∧ smv P σ = false)) ?_
      (fun σ s ⟨⟨h, z⟩, t⟩ => h.weaken fun e => ⟨e, smv_of' z t⟩) fun _ _ h => h
    refine qinv_vp.seq (crt_vp.seq (n_vp.seq (mask_vp.seq (stores_vp.mono (fun σ s h => KF.ss h) ?_))))
    intro σ s ⟨h, r0⟩
    refine ⟨h.bo, ?_, fun i hi => ?_⟩
    · rw [r0, resv_key h.e.2]
      have := b2n_le' (maskv P σ)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      cases maskv P σ <;> rfl
    · rw [h.outs i hi, oExp_eq h.e.2 i hi]

end

end VG.Proof.RsaKeyGen.Arm.Key
