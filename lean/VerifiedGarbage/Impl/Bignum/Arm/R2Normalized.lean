module

public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare

/-! Public normalized-modulus initialization reuses the original R-squared tail. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Set the highest bit of array 4, after clearing that array. -/
def r2TopBit : List Instr :=
  [.ldr .r4 .r0 96, .ldr .r1 .r0 48,
   .dp .add .r4 .r4 (.shifted .r1 .lsl 3), .dp .sub .r4 .r4 (.imm 4),
   .mov .r5 (.imm 0x80000000), .str .r5 .r4 0]

def r2NormalizedConstants : Prog isa :=
  .seq (smallConst 4 0) (.seq (.block r2TopBit) (smallConst 7 2))

/-- The normalized path needs `w+1`, rather than `65*w`, doublings. -/
def r2NormalizedCount : List Instr :=
  [.ldr .r1 .r0 48, .dp .add .r1 .r1 (.imm 1), .str .r1 .r0 208]

/-- Prepare a public normalization decision with the existing array comparison. -/
def r2PublicPrepare : Prog isa :=
  .seq r2NormalizedConstants (.seq (arrayCompare 4 0) (.block [.subs .r11 .r11 (.imm 0)]))

/-- Select only the initialization; both paths share the doubling and squaring tail. -/
def r2PublicInit : Prog isa :=
  .seq r2PublicPrepare (.ite .ne (.block r2NormalizedCount) r2Init)

def r2Public : Prog isa := .seq r2PublicInit (.seq doubleLoop r2Squares)

end VG.Impl.Bignum.Arm
