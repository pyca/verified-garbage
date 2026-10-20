module

public import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
public import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

@[expose] public section

namespace VG.Impl.Ed25519.X86
materialize_code scalarBase
end VG.Impl.Ed25519.X86
