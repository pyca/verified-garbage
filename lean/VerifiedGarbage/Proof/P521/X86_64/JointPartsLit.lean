module
public import VerifiedGarbage.Impl.P521.X86_64.Joint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.P521.X86_64.Joint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit


/-!
# P-521 on x86-64, baseline: the joint verifier's cache and doubling as literals

Both the literal of the joint verifier's code
(`Proof/Ecdsa/Verify/X86_64/P521/JointLit.lean`) and the constant-time
checks of these parts (`JointTiming`) evaluate them: their literals are
checked once here, and both read them.
-/

@[expose] public section

namespace VG.Proof.P521.X86_64
open VG VG.X86_64 VG.Impl.P521.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64

materialize_code jointDoubleCode :=
  fprogB publicJoint.K.M (dblJMul publicJoint.K.S publicJoint.K.R publicJoint.K.D)
materialize_code jointCacheCode := Joint.cacheCode publicJoint

end VG.Proof.P521.X86_64
