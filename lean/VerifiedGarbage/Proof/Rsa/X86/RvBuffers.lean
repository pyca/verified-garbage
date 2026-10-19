module

public import VerifiedGarbage.Proof.Rsa.X86.RvResources

/-! # Public buffer bounds and separation for recovery inputs and outputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

theorem ABI.inputLength {s : State} (a : ABI s) (i : Fin 3) :
    0 < ((caller s).buffer (4 + 2 * i.val)).len ∧
      ((caller s).buffer (4 + 2 * i.val)).len ≤ 8 * (caller s).n := by
  have w := a.width.2.2
  change (arg s 5).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat at w
  have lo := a.lengths.1
  have ep := a.ePositive; have dp := a.dPositive
  have eb := a.eBound; have db := a.dBound
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> rw [e]
  · change 0 < (arg s 5).toNat ∧ (arg s 5).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega
  · change 0 < (arg s 7).toNat ∧ (arg s 7).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega
  · change 0 < (arg s 9).toNat ∧ (arg s 9).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega

theorem ABI.outputLength {s : State} (a : ABI s) (i : Fin 2) :
    0 < ((caller s).buffer (2 * i.val)).len ∧
      ((caller s).buffer (2 * i.val)).len ≤ 8 * (caller s).n := by
  have w := a.width.2.2
  change (arg s 5).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat at w
  have lo := a.lengths.1
  have p := a.pLen; have q := a.qLen
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> rw [e]
  · change 0 < (arg s 1).toNat ∧ (arg s 1).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega
  · change 0 < (arg s 3).toNat ∧ (arg s 3).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega

theorem ABI.inputMember {s : State} (a : ABI s) (i : Fin 3) :
    (caller s).buffer (4 + 2 * i.val) ∈ s.rd := by
  rw [a.rd]
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> simp [e]

theorem ABI.outputMember {s : State} (i : Fin 2) :
    (caller s).buffer (2 * i.val) ∈ [(caller s).buffer 0, (caller s).buffer 2] := by
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> simp [e]

theorem ABI.inputFit {s : State} (a : ABI s) (i : Fin 3) :
    (arg s (4 + 2 * i.val)).toNat + ((caller s).buffer (4 + 2 * i.val)).len ≤ 2 ^ 32 := by
  change (arg s _).toNat + (arg s _).toNat ≤ 2 ^ 32
  apply a.bounds
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> simp [e]

theorem ABI.outputFit {s : State} (a : ABI s) (i : Fin 2) :
    (arg s (2 * i.val)).toNat + ((caller s).buffer (2 * i.val)).len ≤ 2 ^ 32 := by
  change (arg s _).toNat + (arg s _).toNat ≤ 2 ^ 32
  apply a.bounds
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> simp [e]

theorem ABI.outputSeparate {s : State} (a : ABI s) (i j : Fin 2) (ne : i ≠ j) :
    ((caller s).buffer (2 * i.val)).Disjoint ((caller s).buffer (2 * j.val)) := by
  have neq : i.val ≠ j.val := fun h => ne (Fin.ext h)
  have casesI : i.val = 0 ∨ i.val = 1 := by omega
  have casesJ : j.val = 0 ∨ j.val = 1 := by omega
  rcases casesI with e | e <;> rcases casesJ with f | f
  all_goals try omega
  all_goals simp only [e, f, Nat.mul_zero, Nat.mul_one]
  · exact a.outSeparate
  · exact a.outSeparate.symm

end VG.Proof.Rsa.X86.Recover
