module

public import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.Verify
meta import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Ed25519.X86.PointMul
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

@[expose] public section

namespace VG.Impl.Ed25519.X86
materialize_code verifyEquation
end VG.Impl.Ed25519.X86
