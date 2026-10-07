import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian

/-! Signed five-bit NAF recoding of a public 256-bit scalar into 257 bytes. -/
namespace VG.Impl.Weierstrass.AArch64.Naf
open VG VG.AArch64 VG.Impl.Mont.AArch64

def prepInit (K : WinCfg) (src : Nat) : List Instr :=
  [ld .x5 src,ld .x6 (src+8),ld .x7 (src+16),ld .x8 (src+24),
   .movz .x .x9 0 0,.movz .x .x10 31 0,.movz .x .x11 16 0,.movz .x .x12 0 0,
   .movz .x .x13 1 0,.movz .x .x19 257 0,.addImm .x .x20 .x0 K.bits]

def chooseDigit : Prog isa :=
  .seq (.block [.logic .and .x .x1 .x5 .x13]) <|
    .ite (.nonzero .x .x1)
      (.block [.logic .and .x .x2 .x5 .x10,.logic .and .x .x3 .x2 .x11,
        .lsl .x .x3 .x3 1,.sub .x .x2 .x2 .x3])
      (.block [.movz .x .x2 0 0])

def subtractShift : List Instr :=
  [.lsr .x .x3 .x2 63,.sub .x .x3 .x12 .x3,
   .subs .x .x5 .x5 .x2,.sbcs .x .x6 .x6 .x3,.sbcs .x .x7 .x7 .x3,
   .sbcs .x .x8 .x8 .x3,.sbc .x .x9 .x9 .x3,
   .extr .x .x5 .x6 .x5 1,.extr .x .x6 .x7 .x6 1,
   .extr .x .x7 .x8 .x7 1,.extr .x .x8 .x9 .x8 1,.lsr .x .x9 .x9 1]

def prepStep : Prog isa :=
  .seq chooseDigit (.block (([.strb .x2 .x20 0,.addImm .x .x20 .x20 1] : List Instr) ++
    subtractShift ++ [decCounter]))

def prep (K : WinCfg) (src : Nat) : Prog isa :=
  .seq (.block (prepInit K src)) (.loop prepStep (.nonzero .x .x19))

end VG.Impl.Weierstrass.AArch64.Naf
