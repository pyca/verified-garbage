module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
meta import VerifiedGarbage.Impl.X25519.AArch64.AltLadder

/-! # The `_alt` ladder's function as a literal, for the checks that evaluate it -/

@[expose] public section

namespace VG
materialize_code Impl.X25519.AArch64.AltLadder.x25519
end VG
