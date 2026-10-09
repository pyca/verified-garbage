import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64

/-!
# P-384 on x86-64, baseline: the joint verifier's cache and doubling as literals

Both the literal of the joint verifier's code
(`Proof/Ecdsa/Verify/X86_64/P384/JointLit.lean`) and the constant-time
checks of these parts (`JointTiming`) evaluate them: their literals are
checked once here, and both read them.
-/

namespace VG.Proof.P384.X86_64
open VG VG.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64

materialize_code jointDoubleCode :=
  fprogB publicJoint.K.M (dblJMul publicJoint.K.S publicJoint.K.R publicJoint.K.D)
materialize_code jointCacheCode := Naf.cacheTable publicJoint.K.M publicJoint.K.tbl publicJoint.cache 8

end VG.Proof.P384.X86_64
