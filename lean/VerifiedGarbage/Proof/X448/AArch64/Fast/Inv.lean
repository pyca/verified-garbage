import VerifiedGarbage.Proof.X448.AArch64.Fast.Ladder
import VerifiedGarbage.Proof.X448.AArch64.Fast.Chain

/-!
# X448 on AArch64: inversion

Untrusted: everything here is checked by Lean. The addition chain of
`Impl/X448/AArch64/Weak.lean`, with the faster field operations.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot mask)
open VG.Proof.X448.AArch64.Weak (Index Env setCounter_ok decCounter_ok opMul opCopy opSqn opMul_update
  FieldOp applyOps invEnv)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem invert_spec (base : Addr) : ISpec base Impl.X448.AArch64.Fast.invert invEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 14 2] (by simp [MulCopy])).seq <|
    (sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 14 14 2, .copy 15 14] (by simp [MulCopy])).seq <|
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
    (opsI base [.mul 21 21 2] (by simp [MulCopy])).seq <|
    (sqnI base 21 (n := 225) (by decide) (by decide)).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 2, .mul 21 21 20] (by simp [MulCopy]))
  exact h

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa Impl.X448.AArch64.Fast.invert s fun t =>
      IKeep base s t ∧ BEnv t.mem base ∧ EV t.mem base = invEnv (EV s.mem base) :=
  invert_spec base s hs hb

end VG.Proof.X448.AArch64.Fast
