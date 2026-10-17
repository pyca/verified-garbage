module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.Scalar
meta import VerifiedGarbage.Impl.Ed25519.X86.Scalar
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Impl.Ed25519.X86
materialize_code scalarReduce
end VG.Impl.Ed25519.X86
