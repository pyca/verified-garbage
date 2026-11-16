module

public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics
public import VerifiedGarbage.Proof.Sha3.Spec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Sha3.Lanes

/-! ### `Sha3.AArch64.Sha3.Vector.Rho`, which only this module used -/

section

/-! ### `Sha3.AArch64.Sha3.Vector.Theta`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (C D)

def dreg (x : Nat) : VReg := [VReg.v29, .v30, .v31, .v27, .v28].getD x .v29

def ALanes (σ : Low) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), σ (vreg i) = A[i]

def DLanes (σ : Low) (A : Spec.Sha3.State) : Prop :=
  ∀ x < 5, σ (dreg x) = D A x

theorem theta_preserves (σ : Low) (r : VReg) (hr : ∀ x < 7, r ≠ vreg (25 + x)) :
    runLow theta σ r = σ r := by
  obtain h25 := hr 0 (by decide)
  obtain h26 := hr 1 (by decide)
  obtain h27 := hr 2 (by decide)
  obtain h28 := hr 3 (by decide)
  obtain h29 := hr 4 (by decide)
  obtain h30 := hr 5 (by decide)
  obtain h31 := hr 6 (by decide)
  simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at h25 h26 h27 h28 h29 h30 h31
  simp only [runLow, theta, List.foldl_cons, List.foldl_nil, opLow, put,
    h25, h26, h27, h28, h29, h30, h31, ite_false]

theorem theta_lanes (σ : Low) (A : Spec.Sha3.State) (h : ALanes σ A) :
    ALanes (runLow theta σ) A := by
  intro i hi
  rw [theta_preserves]
  · exact h i hi
  · exact (show ∀ i < 25, ∀ x < 7, vreg i ≠ vreg (25 + x) by decide) i hi

/-- The five correction words use RAX1's rotate-left by one. -/
theorem theta_d (σ : Low) (A : Spec.Sha3.State) (h : ALanes σ A) (x : Nat) (hx : x < 5) :
    runLow theta σ (dreg x) = D A x := by
  obtain ha : ∀ i (hi : i < 25), σ (vreg i) = A[i]! := fun i hi => (h i hi).trans
    (VG.Proof.Sha3.getElem!_eq A hi).symm
  -- the lanes, once: not in each of the five cases
  obtain h0 := ha 0 (by decide)
  obtain h1 := ha 1 (by decide)
  obtain h2 := ha 2 (by decide)
  obtain h3 := ha 3 (by decide)
  obtain h4 := ha 4 (by decide)
  obtain h5 := ha 5 (by decide)
  obtain h6 := ha 6 (by decide)
  obtain h7 := ha 7 (by decide)
  obtain h8 := ha 8 (by decide)
  obtain h9 := ha 9 (by decide)
  obtain h10 := ha 10 (by decide)
  obtain h11 := ha 11 (by decide)
  obtain h12 := ha 12 (by decide)
  obtain h13 := ha 13 (by decide)
  obtain h14 := ha 14 (by decide)
  obtain h15 := ha 15 (by decide)
  obtain h16 := ha 16 (by decide)
  obtain h17 := ha 17 (by decide)
  obtain h18 := ha 18 (by decide)
  obtain h19 := ha 19 (by decide)
  obtain h20 := ha 20 (by decide)
  obtain h21 := ha 21 (by decide)
  obtain h22 := ha 22 (by decide)
  obtain h23 := ha 23 (by decide)
  obtain h24 := ha 24 (by decide)
  simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
  obtain rfl | rfl | rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega_using [hx]
  all_goals
    simp only [runLow, theta, List.foldl_cons, List.foldl_nil, opLow, put, dreg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ↓reduceIte]
  all_goals
    simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,
      D, C, VG.Proof.Sha3.rotateLeft_eq _ (by decide : 0 < 1) (by decide : 1 < 64),
      Nat.reduceAdd, Nat.reduceMod]
    rw [BitVec.xor_comm]
    congr 1 <;> ac_rfl

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

end


@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Proof.Sha3 (B rotl)

def BLanes (σ : Low) (A : Spec.Sha3.State) : Prop :=
  ∀ i < 25, σ (breg i) = B A (i % 5) (i / 5)

theorem rho_lanes (σ : Low) (A : Spec.Sha3.State) (hA : ALanes σ A) (hD : DLanes σ A) :
    BLanes (runLow rhoPi σ) A := by
  obtain ha : ∀ i (hi : i < 25), σ (vreg i) = A[i]! := fun i hi => (hA i hi).trans
    (VG.Proof.Sha3.getElem!_eq A hi).symm
  obtain a0 := ha 0 (by decide)
  obtain a1 := ha 1 (by decide)
  obtain a2 := ha 2 (by decide)
  obtain a3 := ha 3 (by decide)
  obtain a4 := ha 4 (by decide)
  obtain a5 := ha 5 (by decide)
  obtain a6 := ha 6 (by decide)
  obtain a7 := ha 7 (by decide)
  obtain a8 := ha 8 (by decide)
  obtain a9 := ha 9 (by decide)
  obtain a10 := ha 10 (by decide)
  obtain a11 := ha 11 (by decide)
  obtain a12 := ha 12 (by decide)
  obtain a13 := ha 13 (by decide)
  obtain a14 := ha 14 (by decide)
  obtain a15 := ha 15 (by decide)
  obtain a16 := ha 16 (by decide)
  obtain a17 := ha 17 (by decide)
  obtain a18 := ha 18 (by decide)
  obtain a19 := ha 19 (by decide)
  obtain a20 := ha 20 (by decide)
  obtain a21 := ha 21 (by decide)
  obtain a22 := ha 22 (by decide)
  obtain a23 := ha 23 (by decide)
  obtain a24 := ha 24 (by decide)
  simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
  obtain d0 := hD 0 (by decide)
  obtain d1 := hD 1 (by decide)
  obtain d2 := hD 2 (by decide)
  obtain d3 := hD 3 (by decide)
  obtain d4 := hD 4 (by decide)
  simp only [dreg, List.getD_cons_succ, List.getD_cons_zero] at d0 d1 d2 d3 d4
  -- One `simp` for all the lanes, which simplifies `runLow rhoPi σ` once; each read takes its
  -- branch of a `put` before `simp` visits the other (`↓reduceIte`).
  refine forall_lt_25 ?_
  simp only [runLow, rhoPi, List.foldl_cons, List.foldl_nil, opLow, put, breg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ↓reduceIte,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, d0,d1,d2,d3,d4,
      B, piSrc, rhoOff, rotl, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, and_self]

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

end


@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (B)

def chiWord (A : Spec.Sha3.State) (i : Nat) : BitVec 64 :=
  B A (i % 5) (i / 5) ^^^
    (B A ((i % 5 + 2) % 5) (i / 5) &&& ~~~(B A ((i % 5 + 1) % 5) (i / 5)))

def CLanes (σ : Low) (A : Spec.Sha3.State) : Prop := ∀ i < 25, σ (vreg i) = chiWord A i

theorem chi_lanes (σ : Low) (A : Spec.Sha3.State) (hB : BLanes σ A) :
    CLanes (runLow chi σ) A := by
  obtain b0 := hB 0 (by decide)
  obtain b1 := hB 1 (by decide)
  obtain b2 := hB 2 (by decide)
  obtain b3 := hB 3 (by decide)
  obtain b4 := hB 4 (by decide)
  obtain b5 := hB 5 (by decide)
  obtain b6 := hB 6 (by decide)
  obtain b7 := hB 7 (by decide)
  obtain b8 := hB 8 (by decide)
  obtain b9 := hB 9 (by decide)
  obtain b10 := hB 10 (by decide)
  obtain b11 := hB 11 (by decide)
  obtain b12 := hB 12 (by decide)
  obtain b13 := hB 13 (by decide)
  obtain b14 := hB 14 (by decide)
  obtain b15 := hB 15 (by decide)
  obtain b16 := hB 16 (by decide)
  obtain b17 := hB 17 (by decide)
  obtain b18 := hB 18 (by decide)
  obtain b19 := hB 19 (by decide)
  obtain b20 := hB 20 (by decide)
  obtain b21 := hB 21 (by decide)
  obtain b22 := hB 22 (by decide)
  obtain b23 := hB 23 (by decide)
  obtain b24 := hB 24 (by decide)
  simp only [breg, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMod, Nat.reduceDiv] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24
  -- One `simp` for all the lanes, which simplifies `runLow chi σ` once (`↓reduceIte` as in `rho_lanes`).
  refine forall_lt_25 ?_
  simp only [and_self, runLow, chi, List.foldl_cons, List.foldl_nil, opLow, put, vreg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ↓reduceIte,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, chiWord, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd]

theorem chiWord_out (A : Spec.Sha3.State) (rc : BitVec 64) (i : Nat) (hi : i < 25) :
    (if i = 0 then chiWord A i ^^^ rc else chiWord A i) =
      (VG.Proof.Sha3.outState A rc)[i] := by
  simp only [VG.Proof.Sha3.outState, Vector.getElem_ofFn, VG.Proof.Sha3.out, chiWord]
  obtain hz : i % 5 = 0 ∧ i / 5 = 0 ↔ i = 0 := by omega_using []
  simp only [hz]
  have hn (v : BitVec 64) : v ^^^ 0xffffffffffffffff = ~~~v := BitVec.xor_allOnes
  simp only [hn, BitVec.and_comm, BitVec.xor_comm]

end VG.Proof.Sha3.AArch64.Sha3.Vector
