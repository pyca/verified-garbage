module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Impl.Dsa.Generation.Layout

/-! Pack generated p, q and g for the existing verified domain check. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

def packArgs (src dst len : Nat) : List Instr :=
  [.ldrSp .x12 40, mov .x2 .x12, movi .x3 src, .add .x .x12 .x12 .x3,
   movi .x3 dst, .add .x .x2 .x2 .x3, movi .x9 len]

def packPart (src dst len : Nat) : Prog isa :=
  .seq (.block (packArgs src dst len)) Random.copyRest

def pack (pLen qLen : Nat) : Prog isa :=
  seqs [packPart VG.Impl.Dsa.Generation.Layout.p VG.Impl.Dsa.Generation.Layout.packed pLen,
    packPart VG.Impl.Dsa.Generation.Layout.q (VG.Impl.Dsa.Generation.Layout.packed + pLen) qLen,
    packPart VG.Impl.Dsa.Generation.Layout.g (VG.Impl.Dsa.Generation.Layout.packed + pLen + qLen) pLen]

end VG.Impl.Dsa.AArch64.Generation
