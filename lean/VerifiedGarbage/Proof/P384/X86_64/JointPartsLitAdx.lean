import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64

/-!
# P-384 on x86-64, with BMI2 and ADX: the joint verifier's cache and doubling as literals

Both the literal of the joint verifier's code
(`Proof/Ecdsa/Verify/X86_64/P384/JointLitAdx.lean`) and the constant-time
checks of these parts (`JointTiming`) evaluate them: their literals are
checked once here, and both read them.
-/

namespace VG.Proof.P384.X86_64
open VG VG.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64

materialize_code jointDoubleAdxCode :=
  fprogB publicJointAdx.K.M (dblJMul publicJointAdx.K.S publicJointAdx.K.R publicJointAdx.K.D)
materialize_code jointCacheAdxCode := Naf.cacheTable publicJointAdx.K.M publicJointAdx.K.tbl publicJointAdx.cache 8

end VG.Proof.P384.X86_64
