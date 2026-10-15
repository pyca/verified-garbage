module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtDifference
public import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
public import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # CRT residue subtraction hides both residues and the secret factor -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt Operand)

theorem crt_difference_ct {base : BitVec 32} {len w M1 M2 : Nat} (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CrtDifferenceInput base len w M1 s ∧ CrtDifferenceInput base len w M2 t ∧ s.sp = t.sp)
      difference (fun _ _ => True) := by
  let P := fun (s t : State) => CrtDifferenceInput base len w M1 s ∧ CrtDifferenceInput base len w M2 t ∧ s.sp = t.sp
  have op1 : Operand 1 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have input (s : State) {M : Nat} (h : CrtDifferenceInput base len w M s) : ReduceOperandReady base len w s := by
    have positive : 0 < M := by have := h.ready.modulus; rw [h.modulus] at this; omega
    exact ⟨h.ready, by rw [h.r2, h.modulus]; exact Nat.mod_lt _ positive,
      by rw [h.one]; exact h.ready.modulus⟩
  have reduce : RelCT isa P (reduceOperand 1) (fun _ _ => True) :=
    (reduceOperand_ct op1 (by decide) (by decide) fit).mono
      (fun s t h => ⟨input s h.1, input t h.2.1, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) {M : Nat} (h : CrtDifferenceInput base len w M s) :
      WP isa (reduceOperand 1) s (ArithmeticReady base len w) :=
    (reduceOperand_ok s h.ready op1 (by decide) (by decide) h.modulus h.odd h.r2 h.one).mono (fun _ j => j.1)
  have reduced := (relCT_keep_sp reduce (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have small : 128 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fit; omega
  exact reduced.seq ((subModArray_ct (o := 5) (a := 6) (b := 1)
    (by decide) (by decide) (by decide) (by decide) small).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
