module

public import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! R-squared setup shares its six Montgomery squares with exponentiation. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.SharedR2
open VG VG.Arm

def squares (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (op 4 4 4) (.seq (op 4 4 4) (.seq (op 4 4 4)
    (.seq (op 4 4 4) (.seq (op 4 4 4) (op 4 4 4)))))

def r2 (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq r2Init (.seq doubleLoop (squares op))

end VG.Impl.Bignum.Arm.SharedR2
