module

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.VerifyLit
import VerifiedGarbage.Proof.P384.X86_64.JointPartsLit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.P384Literals
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.VerifyLit
meta import VerifiedGarbage.Proof.P384.X86_64.JointPartsLit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P384Literals
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ECDSA verification over P-384 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (`spSafe`, the ABI's checks):
the literals of the code (`materialize_code`, `Proof/Framework/Lit.lean`)
are checked once here instead (with BMI2 and ADX: `JointLitAdx`, in
parallel), reading those of the cache and the doubling (`JointPartsLit`).
-/

@[expose] public section

namespace VG

-- The public key's check and the inversion modulo `n`, which the
-- constant-time check of the verifier's prefix (`JointChecks`) reads too.
materialize_code Proof.Ecdsa.Verify.X86_64.P384.jointCheck := Impl.Ecdh.X86_64.Cfg.check Impl.P384.X86_64.p384v
materialize_code Proof.Ecdsa.Verify.X86_64.P384.jointNPow := Impl.Ecdsa.X86_64.Cfg.nPow Impl.P384.X86_64.p384v
materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP384

end VG
