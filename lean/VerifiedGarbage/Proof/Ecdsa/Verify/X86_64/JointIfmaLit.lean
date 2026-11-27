module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.JointIfma
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P256Literals
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.JointIfma
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ECDSA verification over P-256 on x86-64 with AVX512_IFMA: the code as a literal
-/

@[expose] public section

namespace VG
namespace Proof.Ecdsa.Verify.X86_64.JointIfmaLit
open VG.Impl.P256.X86_64 VG.Proof.Weierstrass.X86_64

/-! The literals of `P256Literals`, under the terms the verification's code
has: its configuration is `p256vx`, `p256x` with verification's table of the
generator's multiples, and `materialize_code` finds a literal by its term.
These pieces do not read the table: the two terms are equal by unfolding the
configurations. -/

private noncomputable abbrev nPowVx.lit := P256Literals.nPowAdx.lit
private theorem nPowVx.lit_eq : p256vx.nPow = nPowVx.lit := P256Literals.nPowAdx.lit_eq
private noncomputable abbrev pPowVx.lit := P256Literals.pPowAdx.lit
private theorem pPowVx.lit_eq : p256vx.pPow = pPowVx.lit := P256Literals.pPowAdx.lit_eq
private noncomputable abbrev checkVx.lit := P256Literals.checkAdx.lit
private theorem checkVx.lit_eq : Impl.Ecdh.X86_64.Cfg.check p256vx = checkVx.lit :=
  P256Literals.checkAdx.lit_eq

end Proof.Ecdsa.Verify.X86_64.JointIfmaLit

materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP256Ifma
end VG
