module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QShape

/-! Shape the final L/8 bytes of the concatenated hash contributions. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

def pShapeArgs (len count plen : Nat) : List Instr :=
  [.ldrSp .x2 0, .ldrSp .x12 32,
   .addImm .x .x12 .x12 ((count + 1) * len - plen), movi .x9 plen]

def pShape (len count plen : Nat) : Prog isa :=
  .seq (.block (pShapeArgs len count plen)) qShape

end VG.Impl.Dsa.AArch64.Generation
