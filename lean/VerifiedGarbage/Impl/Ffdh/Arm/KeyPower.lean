module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyPowerDetect
public import VerifiedGarbage.Impl.Bignum.Arm.TwoExp

/-! # Private-key public-value exponentiation

Generator two uses squaring and linear doubling. Other generators use the
supplied generic phase. The dispatch examines public generator data, and
every selected phase processes the complete scalar supplied to it.
-/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.KeyPower
open VG VG.Arm

/-- The generator-two loop calls the supplied shared arithmetic operations. -/
def twoPhase (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Bignum.Arm.TwoExp.phase
    (VG.Impl.Bignum.Arm.TwoExp.initial (op 6 4 7))
    (op 6 6 6) VG.Impl.Bignum.Arm.TwoExp.candidate (op 6 6 7)

def phase (two generic : Prog isa) : Prog isa :=
  .seq detectTwo (Domain.ifFlag two generic)

def power (two generic : Prog isa) : Prog isa :=
  .seq powerImport (phase two generic)

def powerAt (two generic : Prog isa) (bs es ec : Nat) : Prog isa :=
  .seq (.block (Domain.powerArgs bs es ec)) (power two generic)

end VG.Impl.Ffdh.Arm.KeyPower
