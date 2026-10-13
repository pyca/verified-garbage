module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
meta import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code baseStartBlock := (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps) : Prog isa)
materialize_code baseFinishTail := (.block (outputWords 96 8 ++ Impl.X25519.X86.restore) : Prog isa)
end VG.Proof.Ed25519.X86
