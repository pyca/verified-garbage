module

public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # The `_alt` ladder's function as a literal, for the checks that evaluate it -/

@[expose] public section

namespace VG
materialize_code Impl.X25519.AArch64.AltLadder.x25519
end VG
