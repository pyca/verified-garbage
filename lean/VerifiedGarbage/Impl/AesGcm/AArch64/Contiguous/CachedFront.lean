module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast

/-! # Reuse the caller’s prepared GHASH key when starting a contiguous record -/

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous
open VG.AArch64 VG.Impl.Gcm.AArch64.Pmull

/-- The third stack argument points to a table containing the encoded first power at byte 16. -/
def cachedKey : List Instr :=
  [.ldrq (tReg 1) .x8 (pwOff 1),.vop (.ext (sReg 1) (tReg 1) (tReg 1) 8),
    .movz .x .x5 0xc200 3,.vop (.dup .d2 C .x5)]

abbrev cachedFront : Prog isa := .seq (.block [.ldrSp .x8 16]) (Fast.frontWith cachedKey)

end VG.Impl.AesGcm.AArch64.Contiguous
