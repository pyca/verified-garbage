import VerifiedGarbage.Proof.X448.AArch64.Fast.Chain
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation

/-!
# Ed448 verification's equation on AArch64: the square root's power

`root 12` writes only the temporaries of X448's inversion (slots 14–21), the
products' coefficients and the counter `x19` (an `ISpec` of the register-resident
arithmetic, as X448's inversion); slot 21 ends as `rootPow` of slot 12.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64.Weak (Env FieldOp applyOps opMul opCopy opSqn)
open VG.Proof.X448.AArch64.Fast (ISpec MulCopy opsI sqnI)

/-- The slots after `root 12`. -/
def rootEnv (e : Env) : Env :=
  let e := applyOps [.copy 14 12] e
  let e := opSqn 14 1 e
  let e := applyOps [.mul 14 14 12, .copy 15 14] e
  let e := opSqn 15 2 e
  let e := applyOps [.mul 15 15 14, .copy 16 15] e
  let e := opSqn 16 4 e
  let e := applyOps [.mul 16 16 15, .copy 17 16] e
  let e := opSqn 17 8 e
  let e := applyOps [.mul 17 17 16, .copy 18 17] e
  let e := opSqn 18 16 e
  let e := applyOps [.mul 18 18 17, .copy 19 18] e
  let e := opSqn 19 32 e
  let e := applyOps [.mul 19 19 18, .copy 20 19] e
  let e := opSqn 20 64 e
  let e := applyOps [.mul 20 20 19] e
  let e := opSqn 20 64 e
  let e := applyOps [.mul 20 20 19] e
  let e := opSqn 20 16 e
  let e := applyOps [.mul 20 20 17] e
  let e := opSqn 20 8 e
  let e := applyOps [.mul 20 20 16] e
  let e := opSqn 20 4 e
  let e := applyOps [.mul 20 20 15] e
  let e := opSqn 20 2 e
  let e := applyOps [.mul 20 20 14, .copy 21 20] e
  let e := opSqn 21 1 e
  let e := applyOps [.mul 21 21 12] e
  let e := opSqn 21 223 e
  applyOps [.mul 21 21 20] e

theorem root_spec (base : Addr) : ISpec base (root 12) rootEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 14 12] (by simp [MulCopy])).seq <|
    (sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 14 14 12, .copy 15 14] (by simp [MulCopy])).seq <|
    (sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 15 15 14, .copy 16 15] (by simp [MulCopy])).seq <|
    (sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 16 16 15, .copy 17 16] (by simp [MulCopy])).seq <|
    (sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 17 17 16, .copy 18 17] (by simp [MulCopy])).seq <|
    (sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 18 18 17, .copy 19 18] (by simp [MulCopy])).seq <|
    (sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (opsI base [.mul 19 19 18, .copy 20 19] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 17] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 16] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 15] (by simp [MulCopy])).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 14, .copy 21 20] (by simp [MulCopy])).seq <|
    (sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 21 21 12] (by simp [MulCopy])).seq <|
    (sqnI base 21 (n := 223) (by decide) (by decide)).seq
    (opsI base [.mul 21 21 20] (by simp [MulCopy]))
  exact h

theorem rootEnv_eval (e : Env) : rootEnv e 21 = rootPow (e 12) := by
  simp only [↓reduceIte, rootEnv, applyOps, FieldOp.apply, opMul, opCopy, opSqn,
    Function.update_apply]
  rfl

theorem rootEnv_keep (e : Env) (i : Fin 22) (hi : i.val < 14) : rootEnv e i = e i := by
  have h1 : i ≠ 14 := fun h => absurd hi (by rw [h]; decide)
  have h2 : i ≠ 15 := fun h => absurd hi (by rw [h]; decide)
  have h3 : i ≠ 16 := fun h => absurd hi (by rw [h]; decide)
  have h4 : i ≠ 17 := fun h => absurd hi (by rw [h]; decide)
  have h5 : i ≠ 18 := fun h => absurd hi (by rw [h]; decide)
  have h6 : i ≠ 19 := fun h => absurd hi (by rw [h]; decide)
  have h7 : i ≠ 20 := fun h => absurd hi (by rw [h]; decide)
  have h8 : i ≠ 21 := fun h => absurd hi (by rw [h]; decide)
  simp only [rootEnv, applyOps, FieldOp.apply, opMul, opCopy, opSqn, Function.update_of_ne h1,
    Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
    Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne h8]

end VG.Proof.Ed448.AArch64
