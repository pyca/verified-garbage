import VerifiedGarbage.Proof.Ed448.X86.VerifyField
import VerifiedGarbage.Proof.Ed448.Root

/-!
# Ed448 verification's equation on x86 (32-bit): the square root's power

`root`: X448's addition chain for the inversion as far as `z^(2^223 - 1)`,
then 223 squarings and a multiplication, for `z` in slot 12, into slot 21
with the temporaries 14–20: `Proof.Ed448.rootPow`, `z^((p-3)/4)`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86

/-- The field slots after `root`. -/
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

theorem root_spec (base : Addr) : ISpec base root rootEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 14 12]).seq <|
    (sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 14 14 12, .copy 15 14]).seq <|
    (sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19]).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19]).seq <|
    (sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 17]).seq <|
    (sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 16]).seq <|
    (sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 15]).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 14, .copy 21 20]).seq <|
    (sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 21 21 12]).seq <|
    (sqnI base 21 (n := 223) (by decide) (by decide)).seq <|
    (opsI base [.mul 21 21 20])
  exact h

theorem rootEnv_eval (e : Env) : rootEnv e 21 = Proof.Ed448.rootPow (e 12) := by
  simp only [↓reduceIte, rootEnv, applyOps, FieldOp.apply, opMul, opCopy, opSqn,
    Function.update_apply]
  rfl

theorem rootEnv_keep (e : Env) (i : Index) (hi : i.val < 14) : rootEnv e i = e i := by
  have h14 : i ≠ 14 := fun h => by subst h; omega
  have h15 : i ≠ 15 := fun h => by subst h; omega
  have h16 : i ≠ 16 := fun h => by subst h; omega
  have h17 : i ≠ 17 := fun h => by subst h; omega
  have h18 : i ≠ 18 := fun h => by subst h; omega
  have h19 : i ≠ 19 := fun h => by subst h; omega
  have h20 : i ≠ 20 := fun h => by subst h; omega
  have h21 : i ≠ 21 := fun h => by subst h; omega
  simp only [rootEnv, applyOps, FieldOp.apply, opMul, opCopy, opSqn,
    Function.update_of_ne h21, Function.update_of_ne h14, Function.update_of_ne h15,
    Function.update_of_ne h16, Function.update_of_ne h17, Function.update_of_ne h18,
    Function.update_of_ne h19, Function.update_of_ne h20]

theorem root_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa root s fun t =>
      IKeep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = rootEnv (E s.mem base) :=
  root_spec base s hs hb

end VG.Proof.Ed448.X86
