module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random

/-! Copy the seed digest and set the subgroup candidate's endpoint bits. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

def qShapeEnds : List Instr :=
  [.ldrb .x0 .x13 0, movi .x4 128, .logic .orr .x .x0 .x0 .x4,
   .strb .x0 .x13 0, .add .x .x2 .x13 .x14, .subImm .x .x2 .x2 1,
   .ldrb .x0 .x2 0, movi .x4 1, .logic .orr .x .x0 .x0 .x4, .strb .x0 .x2 0]

/-- x12 is the digest, x2 its destination, and x9 its public byte length. -/
def qShape : Prog isa :=
  .seq (.block [mov .x13 .x2, mov .x14 .x9])
    (.seq Random.copyRest (.block qShapeEnds))

end VG.Impl.Dsa.AArch64.Generation
