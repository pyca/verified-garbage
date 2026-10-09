import VerifiedGarbage.Impl.Zeroize.AArch64

namespace VG.Impl.Zeroize.AArch64
open VG.AArch64

/-- Eight full-width stores per iteration; scalar loops handle the remainder. -/
def wideStep : List Instr :=
  [.strq .v0 .x0 0, .strq .v0 .x0 16, .strq .v0 .x0 32, .strq .v0 .x0 48,
   .strq .v0 .x0 64, .strq .v0 .x0 80, .strq .v0 .x0 96, .strq .v0 .x0 112,
   .addImm .x .x0 .x0 128, .subImm .x .x3 .x3 1]

def wideLoop : Prog isa :=
  .ite (.zero .x .x3) (.block []) (.loop (.block wideStep) (.nonzero .x .x3))

def zeroizeWide : Prog isa :=
  .seq (.block [.movz .x .x2 0 0, .lsr .x .x3 .x1 7, .movz .x .x4 127 0,
    .logic .and .x .x1 .x1 .x4, .vop (.dup .d2 .v0 .x2)])
  (.seq wideLoop
  (.seq (.block [.lsr .x .x3 .x1 3, .movz .x .x4 7 0, .logic .and .x .x1 .x1 .x4])
  (.seq (loop true) (.seq (.block [.addImm .x .x3 .x1 0]) (loop false)))))
end VG.Impl.Zeroize.AArch64
