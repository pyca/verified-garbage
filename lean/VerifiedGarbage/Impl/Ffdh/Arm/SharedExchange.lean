module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare

/-! Shared-secret exponentiation calls the existing RSA Montgomery helper. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Impl.Ffdh.Arm.Domain

def finish : Prog isa := .seq (.block Exchange.saveResult)
  (.seq Exchange.exportResult Exchange.maskOutput)

def main (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt op 24)
    (.seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt op 36 40 44)
      (.seq (VG.Impl.Ffdh.Arm.inRange 6) finish))

def code (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.Arm.framed (.seq (.block Exchange.entry) (head (main op)))

end VG.Impl.Ffdh.Arm.SharedExchange
