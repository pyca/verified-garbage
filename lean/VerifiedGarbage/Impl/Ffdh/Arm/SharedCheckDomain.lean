module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! Imported domain validation through the shared RSA Montgomery helper.

`vg_ffdh_check_domain`: the vetted standard groups first, then the modulus
shape, the generator's range and, with a subgroup order, q's range and
parity, q dividing p − 1 and g's membership, each Montgomery product a
call of `op`. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.SharedCheckDomain
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Ffdh.Arm.Domain

/-- `reduceOperand o` by the product `op`: array `o` modulo the modulus,
by its encoding (array 4 holds R²) and its decoding (array 7 holds one). -/
def reduce (op : Nat → Nat → Nat → Prog isa) (o : Nat) : Prog isa := .seq (op o o 4) (op o o 7)

/-- Since q>2, checking p mod q=1 is equivalent to q dividing p-1. -/
def divides (op : Nat → Nat → Nat → Prog isa) (dbl : Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt op dbl 60) (.seq (importAt 1 24 32)
    (.seq (smallConst 7 1) (.seq (reduce op 1) (VG.Impl.Ffdh.Arm.isOne 1))))

def generator (op : Nat → Nat → Nat → Prog isa) (dbl : Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt op dbl 24)
    (.seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup op 56) finishFlag)

def qChecks (op : Nat → Nat → Nat → Prog isa) (dbl : Prog isa) : Prog isa := .seq CheckDomain.qRange (ifFlag
  (.seq (divides op dbl) (ifFlag (generator op dbl) (ret 0))) (ret 0))

def main (op : Nat → Nat → Nat → Prog isa) (dbl : Prog isa) : Prog isa :=
  .seq (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt op dbl 24) (.seq (importAt 1 56 32)
    (.seq (VG.Impl.Ffdh.Arm.inRange 1) (ifFlag (withQ (qChecks op dbl) (ret 1)) (ret 0))))

def body (op : Nat → Nat → Nat → Prog isa) (dbl : Prog isa) : Prog isa := .seq VG.Impl.Ffdh.Arm.VettedGroups.code
  (.seq testFlag (.ite .ne (ret 1) (head (main op dbl))))

def code (op : Nat → Nat → Nat → Prog isa) (dbl : Prog isa) : Prog isa :=
  VG.Impl.Ffdh.Arm.framed (.seq (.block CheckDomain.entry) (body op dbl))

end VG.Impl.Ffdh.Arm.SharedCheckDomain
