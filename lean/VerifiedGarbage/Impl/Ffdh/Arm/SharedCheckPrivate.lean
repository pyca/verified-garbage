module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic

/-! Imported private-key validation through the shared RSA Montgomery helper.

`vg_ffdh_check_private`: the scalar's range (the one branch on x, which its
status discloses), the public value's range and, with a subgroup order, its
membership, then `g^x mod p` over x's `x_len` bytes compared with the public
value, as `Domain.CheckPrivate` did with its own arithmetic. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.SharedCheckPrivate
open VG VG.Arm VG.Impl.Ffdh.Arm.Domain

/-- `g^x mod p` over x's `x_len` bytes, compared with the public value. -/
def matchPublic (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt op 56 40 44)
    (.seq (importAt 1 36 32) (.seq (VG.Impl.Ffdh.Arm.equal 6 1) finishFlag))

def tail (op : Nat → Nat → Nat → Prog isa) : Prog isa := withQ
  (.seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup op 36) (ifFlag (matchPublic op) (ret 0)))
  (matchPublic op)

def publicCheck (op : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (importAt 1 36 32)
  (.seq (VG.Impl.Ffdh.Arm.inRange 1) (ifFlag (tail op) (ret 0)))

def main (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt op 24) (.seq (importAt 1 40 44)
    (.seq CheckPrivate.scalarRange (ifFlag (publicCheck op) (ret 2))))

def code (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.Arm.framed (.seq (.block CheckPrivate.entry) (head (main op)))

end VG.Impl.Ffdh.Arm.SharedCheckPrivate
