module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
meta import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Impl.Ed25519.X86
materialize_code scalarMulAdd
end VG.Impl.Ed25519.X86
