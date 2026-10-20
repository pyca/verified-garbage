module

import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
meta import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
meta import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! A checked literal for the complete verification program. -/

@[expose] public section

namespace VG

materialize_code verifyEquationLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.baseline
  (Impl.Ed25519.X86_64.windows Impl.X25519.X86_64.baseline))
materialize_code verifyEquationAdxLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
  (Impl.Ed25519.X86_64.windows Impl.X25519.X86_64.adx))
materialize_code verifyEquationIfmaLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
  Impl.Ed25519.X86_64.Ifma.windows)

end VG
