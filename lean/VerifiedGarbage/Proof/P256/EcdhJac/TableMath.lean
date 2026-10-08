import VerifiedGarbage.Impl.P256.EcdhJac
import VerifiedGarbage.Proof.Weierstrass.JacCoZ
import VerifiedGarbage.Proof.Weierstrass.Env

namespace VG.Proof.P256.EcdhJac
open VG VG.Impl.Weierstrass VG.Proof.Weierstrass
open VG.Impl.P256.EcdhJac

def tblW : List Nat :=
  [K.D.x,K.D.y,K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5,K.E.x,K.E.y,K.E.z,z2,zz]
def tblσ (i : Nat) : Nat := (tblW++[K.P.x,K.P.y,K.P.z]).getD i K.P.x

/-- DBLU on numbered slots (`tblσ`). -/
def dbluN : List FOp :=
  [.mul 2 13 13, .mul 3 14 14, .mul 4 3 3, .mul 5 13 3, .add 5 5 5, .add 5 5 5, .sub 6 2 15,
   .add 7 6 6, .add 6 7 6, .mul 8 6 6, .sub 8 8 5, .sub 8 8 5, .sub 7 5 8, .mul 9 6 7,
   .add 4 4 4, .add 4 4 4, .add 4 4 4, .sub 9 9 4, .add 10 14 14, .mul 11 10 10, .mul 12 11 10]

/-- ZADDU on numbered slots (`tblσ`). -/
def zadduN : List FOp :=
  [.sub 2 0 8, .mul 3 2 2, .mul 10 10 2, .mul 0 0 3, .mul 5 8 3, .sub 6 1 9, .mul 7 6 6,
   .sub 4 0 5, .mul 1 1 4, .sub 8 7 0, .sub 8 8 5, .sub 9 0 8, .mul 9 6 9, .sub 9 9 1,
   .mul 11 11 3, .mul 12 11 10]


theorem dblu_eq : dbluOps=dbluN.map (FOp.rename tblσ) := rfl
theorem zaddu_eq : zadduOps=zadduN.map (FOp.rename tblσ) := rfl

/-- DBLU from `P = (x, y, 1)`: `T = 2 P` with its powers, and `(t3, t2)` is
`P` scaled by `T`'s `Z`. -/
theorem dbluN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) (h15 : e 15 = 1) :
    (runOps dbluN e 8, runOps dbluN e 9, runOps dbluN e 10) = dblJF (e 13) (e 14) 1 ∧
      runOps dbluN e 11 = runOps dbluN e 10 * runOps dbluN e 10 ∧
      runOps dbluN e 12 = runOps dbluN e 11 * runOps dbluN e 10 ∧
      runOps dbluN e 5 * (1 * 1) = e 13 * (runOps dbluN e 10 * runOps dbluN e 10) ∧
      runOps dbluN e 4 * (1 * 1 * 1) =
        e 14 * (runOps dbluN e 10 * runOps dbluN e 10 * runOps dbluN e 10) := by
  simp only [dbluN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h15, dblJF, Prod.mk.injEq]
  refine ⟨⟨?_, ?_, ?_⟩, trivial, trivial, ?_, ?_⟩ <;> grind

/-- ZADDU of `D = (X1, Y1)` and `T = (X2, Y2)` sharing `Z`, with `T`'s powers. -/
theorem zadduN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    ((runOps zadduN e 8, runOps zadduN e 9, runOps zadduN e 10), (runOps zadduN e 0, runOps zadduN e 1)) =
        zadduF (e 0) (e 1) (e 8) (e 9) (e 10) ∧
      (e 11 = e 10 * e 10 → runOps zadduN e 11 = runOps zadduN e 10 * runOps zadduN e 10) ∧
      runOps zadduN e 12 = runOps zadduN e 11 * runOps zadduN e 10 := by
  simp only [zadduN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, zadduF]
  refine ⟨?_, fun h => ?_, ?_⟩ <;> first | trivial | grind


end VG.Proof.P256.EcdhJac
