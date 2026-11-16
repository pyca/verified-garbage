module

public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P384Literals
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P384Literals
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64

/-!
# ECDSA verification over P-384 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

namespace VG

namespace Proof.Ecdsa.Verify.AArch64.P384
open VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64

/-- `P384Joint.verify` with its `let c := p384` written out. With the
configuration bound by a `let`, none of the code's parts is a closed term:
`materialize_code` finds neither their literals (`P384Literals`' `validate`,
`nPow`, …) nor the templates of the field operations in it, and the kernel
builds them all again. -/
def verifyCode : Prog isa :=
  .seq (.block (Cfg.args p384)) <| .seq (VG.Impl.Ecdh.AArch64.Cfg.prefixWith p384 (some D)) <|
  .seq (.block (Cfg.loadS p384)) <| .seq (.block (VG.Impl.Ecdh.AArch64.Cfg.peer p384)) <|
  .seq (VG.Impl.Ecdh.AArch64.Cfg.validate p384) <|
  .seq (Cfg.scalars p384) <| .seq p384.nPow <| .seq (Cfg.uv p384) <|
  .seq P384Joint.points (Cfg.tail p384)

materialize_code verifyCode

/-- `verifyCode`'s literal under the name of the code it is: equal to it by
unfolding both, which `materialize_code` then reads for `verifyP384`. -/
noncomputable abbrev jointVerify.lit := verifyCode.lit
theorem jointVerify.lit_eq : P384Joint.verify = jointVerify.lit := verifyCode.lit_eq

end Proof.Ecdsa.Verify.AArch64.P384

materialize_code Impl.Ecdsa.Verify.AArch64.verifyP384

end VG
