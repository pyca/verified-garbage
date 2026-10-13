module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# P-521 on x86-64, with BMI2 and ADX: the joint verifier's cache and doubling as literals

Both the literal of the joint verifier's code
(`Proof/Ecdsa/Verify/X86_64/P521/JointLitAdx.lean`) and the constant-time
checks of these parts (`JointTiming`) evaluate them: their literals are
checked once here, and both read them.
-/

@[expose] public section

namespace VG.Proof.P521.X86_64
open VG VG.X86_64 VG.Impl.P521.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64

materialize_code jointDoubleAdxCode :=
  fprogB publicJointAdx.K.M (dblJMul publicJointAdx.K.S publicJointAdx.K.R publicJointAdx.K.D)
materialize_code jointCacheAdxCode := Joint.cacheCode publicJointAdx

end VG.Proof.P521.X86_64
