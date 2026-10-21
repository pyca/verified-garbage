module
public import VerifiedGarbage.Proof.Rsa.X86.CvABI

import VerifiedGarbage.Proof.Rsa.X86.CvResources
public import Init.Data.List.Basic
public import VerifiedGarbage.TCB.X86.State

/-! # Public buffer bounds and separation for CRT inputs and outputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

theorem ABI.inputLength {s : State} (a : ABI s) (i : Fin 4) :
    0 < ((caller s).buffer (6 + 2 * i.val)).len ∧
      ((caller s).buffer (6 + 2 * i.val)).len ≤ 8 * (caller s).n := by
  have w := a.width.2.2
  change (arg s 7).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat at w
  have lo := a.lengths.1
  have p := a.pPositive; have q := a.qPositive; have d := a.dPositive
  have ps := a.pSmall; have qs := a.qSmall; have ds := a.dBound
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases cases with e | e | e | e <;> rw [e]
  · change 0 < (arg s 7).toNat ∧ (arg s 7).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega
  · change 0 < (arg s 9).toNat ∧ (arg s 9).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega
  · change 0 < (arg s 11).toNat ∧ (arg s 11).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega
  · change 0 < (arg s 13).toNat ∧ (arg s 13).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega

theorem ABI.outputLength {s : State} (a : ABI s) (i : Fin 3) :
    0 < ((caller s).buffer (2 * i.val)).len ∧
      ((caller s).buffer (2 * i.val)).len ≤ 8 * (caller s).n := by
  have w := a.width.2.2
  change (arg s 7).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat at w
  have p := a.pPositive; have q := a.qPositive
  have ps := a.pSmall; have qs := a.qSmall
  have dp := a.dpLen; have dq := a.dqLen; have qi := a.qiLen
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> rw [e]
  · change 0 < (arg s 1).toNat ∧ (arg s 1).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega
  · change 0 < (arg s 3).toNat ∧ (arg s 3).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega
  · change 0 < (arg s 5).toNat ∧ (arg s 5).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega

theorem ABI.inputMember {s : State} (a : ABI s) (i : Fin 4) :
    (caller s).buffer (6 + 2 * i.val) ∈ s.rd := by
  rw [a.rd]
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases cases with e | e | e | e <;> simp [e]

theorem ABI.outputMember {s : State} (i : Fin 3) :
    (caller s).buffer (2 * i.val) ∈ [(caller s).buffer 0, (caller s).buffer 2, (caller s).buffer 4] := by
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> simp [e]

theorem ABI.inputFit {s : State} (a : ABI s) (i : Fin 4) :
    (arg s (6 + 2 * i.val)).toNat + ((caller s).buffer (6 + 2 * i.val)).len ≤ 2 ^ 32 := by
  change (arg s _).toNat + (arg s _).toNat ≤ 2 ^ 32
  apply a.bounds
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases cases with e | e | e | e <;> simp [e]

theorem ABI.outputFit {s : State} (a : ABI s) (i : Fin 3) :
    (arg s (2 * i.val)).toNat + ((caller s).buffer (2 * i.val)).len ≤ 2 ^ 32 := by
  change (arg s _).toNat + (arg s _).toNat ≤ 2 ^ 32
  apply a.bounds
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> simp [e]

theorem three_outputs {r : Nat → Region}
    (h : (r 0).Disjoint (r 2) ∧ (r 0).Disjoint (r 4) ∧ (r 2).Disjoint (r 4))
    (i j : Fin 3) (ne : i ≠ j) : (r (2 * i.val)).Disjoint (r (2 * j.val)) := by
  have neq : i.val ≠ j.val := fun h => ne (Fin.ext h)
  have casesI : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  have casesJ : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases casesI with e | e | e <;> rcases casesJ with f | f | f
  all_goals try omega
  all_goals simp only [e, f, Nat.mul_zero, Nat.mul_one, show 2 * 2 = 4 from rfl]
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2 |
    exact h.1.symm | exact h.2.1.symm | exact h.2.2.symm

theorem ABI.outputSeparate {s : State} (a : ABI s) (i j : Fin 3) (ne : i ≠ j) :
    ((caller s).buffer (2 * i.val)).Disjoint ((caller s).buffer (2 * j.val)) :=
  three_outputs a.outSeparate i j ne

end VG.Proof.Rsa.X86.CrtValues
