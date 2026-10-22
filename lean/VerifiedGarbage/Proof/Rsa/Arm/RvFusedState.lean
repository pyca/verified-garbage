module

public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
import VerifiedGarbage.Proof.Rsa.Arm.RvCand1
import VerifiedGarbage.Proof.Rsa.RecoverFusedBounds
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Rsa.Arm.RvMont5
public import VerifiedGarbage.Proof.Rsa.RecoverFused

/-! The saved root is canonical: a set bit clears it to zero. This permits
the existing compositional recovery proofs to track a single exact state,
without a second factor-extraction implementation or an existential scratch
value on failure. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Proof.Rsa (b2n)

abbrev fusedKeep : List Nat := [aRoot, mY, mG] ++ liveM
abbrev fusedSlots : List Nat := [sDone, sOk, sCand, sByte, sPtr, sBytes]

def fusedA (P : RP) (j : Nat) (st : VG.Proof.Rsa.Fused.State) : Nat → Nat :=
  upd (upd (upd (AM P) mG ((j + 2) * Rm P % P.n))
    aRoot (st.root.getD 0 * Rm P % P.n)) mY (st.value * Rm P % P.n)

def fusedV (V : Nat → Nat) (st : VG.Proof.Rsa.Fused.State) : Nat → Nat :=
  upd (upd V sDone (b2n st.done)) sOk (b2n st.root.isSome)

abbrev FI (P : RP) (E : State → Prop) (j : Nat) (st : State → VG.Proof.Rsa.Fused.State)
    (V : State → Nat → Nat) : State → State → Prop :=
  St P E (fun σ => fusedA P j (st σ)) fusedKeep (fun σ => AWh P σ P.c) [wR, wM]
    (fun σ => fusedV (V σ) (st σ)) fusedSlots P.w nArr

theorem upd_override (A : Nat → Nat) (j x y : Nat) : upd (upd A j x) j y = upd A j y := by
  funext i
  by_cases eq : i = j <;> simp [upd, eq]

theorem b2n_select (b : Bool) (a c : Nat) :
    (if b2n b = 0 then a else c) = (if b then c else a) := by
  cases b <;> rfl

/-- The two selections used by the implementation update the exact saved root. -/
theorem fused_saved (n b R : Nat) (bit : Bool) (st : VG.Proof.Rsa.Fused.State) :
    (if !st.done && decide (st.value * st.value % n = 1) && !bit then st.value * R % n
      else if bit then 0 else st.root.getD 0 * R % n) =
      (VG.Proof.Rsa.Fused.step n b bit st).root.getD 0 * R % n := by
  cases bit
  · rw [VG.Proof.Rsa.Fused.step_root]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true]
    split <;> rfl
  · simp [VG.Proof.Rsa.Fused.step, VG.Proof.Rsa.Fused.start]

end VG.Proof.Rsa.Arm.Recover
