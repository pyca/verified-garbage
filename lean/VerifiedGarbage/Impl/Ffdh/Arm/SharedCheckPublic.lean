module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedPrepare
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow

/-! Public-key validation through the shared RSA Montgomery helper. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.SharedCheckPublic
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Ffdh.Arm.Domain

def powerAt (op : Nat → Nat → Nat → Prog isa) (bs es ec : Nat) : Prog isa :=
  .seq (.block (powerArgs bs es ec))
    (.seq VG.Impl.Ffdh.Arm.powerImport (SharedWindow.phase op))

/-- The supplied exponent is public; retain only its nonzero suffix. -/
def publicPowerAt (op : Nat → Nat → Nat → Prog isa) (bs es ec : Nat) : Prog isa :=
  .seq (.block (powerArgs bs es ec))
    (.seq VG.Impl.Ffdh.Arm.PublicScan.code
      (.seq VG.Impl.Ffdh.Arm.powerImport (SharedWindow.phase op)))

def subgroup (op : Nat → Nat → Nat → Prog isa) (bs : Nat) : Prog isa :=
  .seq (publicPowerAt op bs 60 32) (VG.Impl.Ffdh.Arm.isOne 6)

def tail (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  withQ (.seq (subgroup op 36) finishFlag) (ret 1)

def main (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt op 24)
    (.seq (importAt 1 36 32) (.seq (inRange 1) (ifFlag (tail op) (ret 0))))

def code (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.Arm.framed (.seq (.block CheckPublic.entry) (head (main op)))

end VG.Impl.Ffdh.Arm.SharedCheckPublic
