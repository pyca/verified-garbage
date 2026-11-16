module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# ECDSA verification over P-521 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

namespace VG

namespace Proof.Ecdsa.Verify.AArch64.P521
open VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64

/-- `P521Joint.verify` with its `let c := p521` written out. With the
configuration bound by a `let`, none of the code's parts is a closed term:
`materialize_code` finds neither their literals (`P521Literals`' `validate`,
`nPow`, …) nor the templates of the field operations in it, and the kernel
builds them all again. -/
def verifyCode : Prog isa :=
  .seq (.block (Cfg.args p521)) <| .seq (VG.Impl.Ecdh.AArch64.Cfg.prefixWith p521 (some D)) <|
  .seq (.block (Cfg.loadS p521)) <| .seq (.block (VG.Impl.Ecdh.AArch64.Cfg.peer p521)) <|
  .seq (VG.Impl.Ecdh.AArch64.Cfg.validate p521) <|
  .seq (Cfg.scalars p521) <| .seq p521.nPow <| .seq (Cfg.uv p521) <|
  .seq P521Joint.points (Cfg.tail p521)

materialize_code verifyCode

/-- `verifyCode`'s literal under the name of the code it is: equal to it by
unfolding both, which `materialize_code` then reads for `verifyP521`. -/
noncomputable abbrev jointVerify.lit := verifyCode.lit
theorem jointVerify.lit_eq : P521Joint.verify = jointVerify.lit := verifyCode.lit_eq

end Proof.Ecdsa.Verify.AArch64.P521

materialize_code Impl.Ecdsa.Verify.AArch64.verifyP521

end VG
