module

public import VerifiedGarbage.Impl.Bignum.Arm.PrepareAcceptedPrime
public import VerifiedGarbage.Impl.Bignum.Arm.SecretPower

/-! # Compute one CRT factor's private power from saved AAPCS arguments -/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

def primePowerArgs (slot : Nat) : List Instr :=
  [.ldrSp .r4 56, .ldrSp .r6 12, .ldrSp .r1 slot, .ldrSp .r2 (slot + 4)]
def primePower (slot : Nat) : Prog isa :=
  .seq prepareAcceptedPrime (.seq (.block (primePowerArgs slot)) secretPower)

end VG.Impl.Bignum.Arm.Crt
