module

public import VerifiedGarbage.Impl.Bignum.Arm.DownRowUmaal

/-! Both ordinary and downward Montgomery rows use the same UMAAL arithmetic. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def umaalArithmetic (c : Prog isa) : Prog isa :=
  Code.subst DownRow.code DownRow.codeU (umaalRows c)

end VG.Impl.Bignum.Arm
