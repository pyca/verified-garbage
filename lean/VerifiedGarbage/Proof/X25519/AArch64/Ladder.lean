module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.X25519.AArch64.Ops
public import Mathlib.Logic.Function.Basic

/-!
# X25519 on AArch64: the ladder

One iteration of the ladder (`step`) takes the ladder's variables in their
slots from `ladderAfter k x1 (t + 1)` to `ladderAfter k x1 t`, for the bit `t`
of the scalar stored at `BITS + t`; the loop (`ladder`) runs it for `t = 254,
…, 0`.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## One iteration -/

/-- Evaluates the slots' values after an operation, so that they refer to the
earlier ones only through their values. -/
macro "vsimp" " at " h:ident : tactic => `(tactic| plain_simp_names simp only [Function.update_apply, lvals, ite_true, ite_false,
                   Nat.reduceEqDiff] at $h:ident)

end VG.Proof.X25519.AArch64

