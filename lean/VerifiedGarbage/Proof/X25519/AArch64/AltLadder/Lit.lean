module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
meta import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The `_alt` ladder's function as a literal, for the checks that evaluate it -/

@[expose] public section

namespace VG
materialize_code Impl.X25519.AArch64.AltLadder.x25519
end VG
