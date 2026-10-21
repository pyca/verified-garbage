module

public import VerifiedGarbage.Proof.Variants.Ffdh.Arm.Base
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic -- shake: keep (exposed backend proof fields reference these lemmas)

/-! Replace each RSA Montgomery row by the proven UMAAL row without changing
any FFDH operation's contract, timing policy, or stack requirement. -/

@[expose] public section
namespace VG.Proof.Variants.Ffdh.Arm.Umaal
open VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : VG.Proof.Ffdh.Arm.Backend where
  checkDomain := umaalArithmetic Base.variant.checkDomain
  checkDomain_verified := umaalArithmetic_verified Base.variant.checkDomain_verified
  checkPublic := umaalArithmetic Base.variant.checkPublic
  checkPublic_verified := umaalArithmetic_verified Base.variant.checkPublic_verified
  checkPrivate := umaalArithmetic Base.variant.checkPrivate
  checkPrivate_verified := umaalArithmetic_verified Base.variant.checkPrivate_verified
  exchange := umaalArithmetic Base.variant.exchange
  exchange_verified := umaalArithmetic_verified Base.variant.exchange_verified
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Variants.Ffdh.Arm.Umaal
