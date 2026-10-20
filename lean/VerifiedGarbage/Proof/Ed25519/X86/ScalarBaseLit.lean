module

public import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
meta import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
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
materialize_code scalarBase
end VG.Impl.Ed25519.X86
