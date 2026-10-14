module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.X25519.AArch64.Hybrid
meta import VerifiedGarbage.Impl.X25519.AArch64.Hybrid
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG
materialize_code Impl.X25519.AArch64.Hybrid.x25519
end VG

namespace VG.Proof.X25519.AArch64.Hybrid
open VG.AArch64

-- The four-word function's setup and output, whose instructions `Top` checks.
materialize_code wordSetup := (.block Impl.X25519.AArch64.Word.setup : Prog isa)
materialize_code wordFinish := (.block Impl.X25519.AArch64.Word.finish : Prog isa)
end VG.Proof.X25519.AArch64.Hybrid
