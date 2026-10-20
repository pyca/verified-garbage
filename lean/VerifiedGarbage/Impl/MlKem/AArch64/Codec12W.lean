module

public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16

/-!
# ByteEncode₁₂ and ByteDecode₁₂ of polynomials stored with 16 bits, on AArch64

Eight coefficients per iteration, as `Codec16.enc` and `Codec16.dec` do with
32-bit coefficients, whose arithmetic (`encMath`, `decMath`) they share:

* `encW(f = x0, out = x1)`: eight halfwords of `f` widened to words by ZIP1
  and ZIP2 with zero (`v17`), then packed into twelve bytes by `encMath`.
* `decW(b = x0, f = x1)`: twelve bytes of `b` decoded to eight words by
  `decMath`, and narrowed to halfwords by UZP1.

Both count their iterations in `x11`.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Codec12W
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Codec16

def encBodyW : List Instr :=
  [.ldrq .v4 .x0 0, .vop (.perm .zip1 .h8 .v0 .v4 .v17), .vop (.perm .zip2 .h8 .v1 .v4 .v17)] ++ encMath ++
  [.str .x .x9 .x1 0, .str .w .x10 .x1 8, .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 12,
   .subImm .x .x11 .x11 1]

def encW : Prog isa :=
  .seq (.block (maskVec .v16 [0,1,2,4,5,6,8,9,10,12,13,14] ++ [.vop (.movi0 .v17), .movz .x .x11 32 0]))
    (.loop (.block encBodyW) (.nonzero .x .x11))

def decBodyW : List Instr :=
  [.ldr .x .x9 .x0 0, .ldr .w .x10 .x0 8] ++ decMath ++
  [.vop (.perm .uzp1 .h8 .v0 .v0 .v1), .strq .v0 .x1 0, .addImm .x .x0 .x0 12, .addImm .x .x1 .x1 16,
   .subImm .x .x11 .x11 1]

def decW : Prog isa :=
  .seq (.block (maskVec .v16 [0,1,2,255,3,4,5,255,6,7,8,255,9,10,11,255] ++
    [.movz .x .x9 4095 0, .vop (.dup .s4 .v17 .x9), .movz .x .x9 3329 0, .vop (.dup .s4 .v18 .x9),
     .movz .x .x11 32 0]))
    (.loop (.block decBodyW) (.nonzero .x .x11))

end VG.Impl.MlKem.AArch64.Codec12W
