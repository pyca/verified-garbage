module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Impl.Bignum.Arm.SharedPrecompute
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! # FFDH modulus preparation with shared Montgomery arithmetic -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.SharedPrepare
open VG VG.Arm

def code (op : Nat → Nat → Nat → Prog isa) (dbl : Prog isa) : Prog isa :=
  .seq VG.Impl.Bignum.Arm.PublicFn.prepare (VG.Impl.Bignum.Arm.SharedPrecompute.precompute op dbl)

def prepareAt (op : Nat → Nat → Nat → Prog isa) (dbl : Prog isa) (slot : Nat) : Prog isa :=
  .seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs slot)) (code op dbl)

end VG.Impl.Ffdh.Arm.SharedPrepare
