module

public import VerifiedGarbage.Proof.Variants.Ffdh.Arm.Base
public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal

/-! Replace each RSA Montgomery row by the proven UMAAL row without changing
any FFDH operation's contract, timing policy, or stack requirement. -/

@[expose] public section
namespace VG.Proof.Variants.Ffdh.Arm.Umaal
open VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : VG.Proof.Ffdh.Arm.Backend where
  checkDomain := umaalRows Base.variant.checkDomain
  checkDomain_verified := umaalRows_verified Base.variant.checkDomain_verified
  checkPublic := umaalRows Base.variant.checkPublic
  checkPublic_verified := umaalRows_verified Base.variant.checkPublic_verified
  checkPrivate := umaalRows Base.variant.checkPrivate
  checkPrivate_verified := umaalRows_verified Base.variant.checkPrivate_verified
  exchange := umaalRows Base.variant.exchange
  exchange_verified := umaalRows_verified Base.variant.exchange_verified
  generateKey := umaalRows Base.variant.generateKey
  generateKey_verified := umaalRows_verified Base.variant.generateKey_verified
  keyStack := Nat.le_trans (armStack_umaalRows _) Base.variant.keyStack
  suffix := "_umaal"
  features := ["umaal"]

end VG.Proof.Variants.Ffdh.Arm.Umaal
