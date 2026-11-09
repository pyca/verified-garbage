module
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Impl.Weierstrass.Layout.Point

/-! Signed five-bit NAF recoding of a public 256-bit scalar into 257 bytes. -/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.Naf
open VG VG.AArch64 VG.Impl.Mont.AArch64

def subtractShift : List Instr :=
  [.lsr .x .x3 .x2 63,.sub .x .x3 .x12 .x3,
   .subs .x .x5 .x5 .x2,.sbcs .x .x6 .x6 .x3,.sbcs .x .x7 .x7 .x3,
   .sbcs .x .x8 .x8 .x3,.sbc .x .x9 .x9 .x3,
   .extr .x .x5 .x6 .x5 1,.extr .x .x6 .x7 .x6 1,
   .extr .x .x7 .x8 .x7 1,.extr .x .x8 .x9 .x8 1,.lsr .x .x9 .x9 1]

end VG.Impl.Weierstrass.AArch64.Naf
