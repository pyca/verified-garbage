module

public import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.Verify
meta import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Impl.Ed25519.X86
materialize_code verifyEquation
end VG.Impl.Ed25519.X86
