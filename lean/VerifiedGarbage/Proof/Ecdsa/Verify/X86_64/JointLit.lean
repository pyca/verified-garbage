module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Templates
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # ECDSA verification over P-256 on x86-64, the joint method: the code as literals

The code without BMI2 and ADX reads the templates of its field operations
(`P256Templates`): `jointVerifyP256`'s check is then a tenth of what it was.
The code with them has its own products, which those templates do not
match, and only pays for looking for them, less than a module of its own
would cost. -/

@[expose] public section

namespace VG
namespace Proof.Ecdsa.Verify.X86_64.JointLit
open VG.Impl.P256.X86_64 VG.Proof.Weierstrass.X86_64

/-! The literals of `P256Literals`, under the terms the verifications' code
has: their configurations are `p256v` and `p256vx`, `p256` and `p256x` with
verification's table of the generator's multiples, and `materialize_code`
finds a literal by its term. These pieces do not read the table: the two
terms are equal by unfolding the configurations. -/

private noncomputable abbrev nPowV.lit := P256Literals.nPow.lit
private theorem nPowV.lit_eq : p256v.nPow = nPowV.lit := P256Literals.nPow.lit_eq
private noncomputable abbrev pPowV.lit := P256Literals.pPow.lit
private theorem pPowV.lit_eq : p256v.pPow = pPowV.lit := P256Literals.pPow.lit_eq
private noncomputable abbrev checkV.lit := P256Literals.check.lit
private theorem checkV.lit_eq : Impl.Ecdh.X86_64.Cfg.check p256v = checkV.lit :=
  P256Literals.check.lit_eq

private noncomputable abbrev nPowVx.lit := P256Literals.nPowAdx.lit
private theorem nPowVx.lit_eq : p256vx.nPow = nPowVx.lit := P256Literals.nPowAdx.lit_eq
private noncomputable abbrev pPowVx.lit := P256Literals.pPowAdx.lit
private theorem pPowVx.lit_eq : p256vx.pPow = pPowVx.lit := P256Literals.pPowAdx.lit_eq
private noncomputable abbrev checkVx.lit := P256Literals.checkAdx.lit
private theorem checkVx.lit_eq : Impl.Ecdh.X86_64.Cfg.check p256vx = checkVx.lit :=
  P256Literals.checkAdx.lit_eq

end Proof.Ecdsa.Verify.X86_64.JointLit

materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP256
materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP256Adx
end VG
