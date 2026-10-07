import VerifiedGarbage.Impl.Bignum.X86_64.MontFn
import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare

/-!
# Montgomery multiplication as a function, with BMI2 and ADX (x86-64)

`vg_rsa_mont_mul_adx(ws, ws_len, o, a, b)`: `vg_rsa_mont_mul` by the tiled
ADX multiplication, for `w` a multiple of 8, and by the baseline's otherwise.

The ADX code reads the bases of its operands from the header at every row,
from the slot of a fixed index (`sArr X`), when every register is in use; so
the function writes the bases of the arrays `o`, `a` and `b`, given at run
time, into the slots of the indices 8, 9 and 10 (header words 16–18, the
functions' own), and runs the ADX code for those indices. It saves header
words 16–21 in `xmm3`–`xmm5` first and writes them back before it returns,
so that it changes only `aAcc`, `aTmp` and `o`. Squares (`a = b`, which the
indices tell, and so publicly) take the triangular tiles.

As `vg_rsa_mont_mul`, it uses no stack and keeps `rbx`, `rbp` and `r12`–`r15`
in `xmm0`–`xmm2` while it runs; it moves them back through header words
16–21, at addresses from `rdi` alone.
-/

namespace VG.Impl.Bignum.X86_64.MontFn

open VG.X86_64 VG.Impl.Bignum.X86_64.Public

/-- The indices whose header slots get the bases of `o`, `a` and `b`. -/
def xO : Nat := 8
def xA : Nat := 9
def xB : Nat := 10

/-- Header words 16–21 (`sFn 0`–`sFn 5`) into `xmm3`–`xmm5`, and the bases of
the arrays in `edx`, `ecx` and `r8d` into the slots of `xO`, `xA` and `xB`
(`sFn 0`–`sFn 2`). -/
def slotsIn : List Instr :=
  [.movdquLoad .xmm3 (hdr (sFn 0)), .movdquLoad .xmm4 (hdr (sFn 2)), .movdquLoad .xmm5 (hdr (sFn 4)),
    .mov .rax (.mem (arrAt .rdx)), .store (hdr (sArr xO)) .rax,
    .mov .rax (.mem (arrAt .rcx)), .store (hdr (sArr xA)) .rax,
    .mov .rax (.mem (arrAt .r8)), .store (hdr (sArr xB)) .rax]

/-- The callee-saved registers from `xmm0`–`xmm2` through header words 16–21,
and those words back from `xmm3`–`xmm5`: every address is `rdi`'s. -/
def restore : List Instr :=
  [.movdquStore (hdr (sFn 0)) .xmm0, .movdquStore (hdr (sFn 2)) .xmm1, .movdquStore (hdr (sFn 4)) .xmm2,
    .mov .rbx (.mem (hdr (sFn 0))), .mov .rbp (.mem (hdr (sFn 1))), .mov .r12 (.mem (hdr (sFn 2))),
    .mov .r13 (.mem (hdr (sFn 3))), .mov .r14 (.mem (hdr (sFn 4))), .mov .r15 (.mem (hdr (sFn 5))),
    .movdquStore (hdr (sFn 0)) .xmm3, .movdquStore (hdr (sFn 2)) .xmm4, .movdquStore (hdr (sFn 4)) .xmm5]

/-- ZF set when `w` is a multiple of 8 in `8..2^30 + 8`: `v = w - 8` (modulo
`2⁶⁴`) rotated right by 3 has its low bits on top, and the rest below `2²⁷`. -/
def alignTest : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .sub .rax (.imm 8), .shift .ror .rax 3, .shift .shr .rax 27]

/-- The tiles: the square's if `a = b`, the product's otherwise. -/
def tiled : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.reg .r8)])
    (.ite .e (AdxTiledSquare.montSquare xO xA) (AdxTiledProduct.montMul xO xA xB))

/-- The tiles for `w` a multiple of 8 (below `2^30 + 8`), `montMul` otherwise. -/
def adxBody : Prog isa :=
  .seq (.block alignTest)
    (.ite .e tiled (.seq (.block basesR) (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))))

/-- `vg_rsa_mont_mul_adx`. -/
def mulAdx : Prog isa :=
  .seq (.block (enter ++ slotsIn)) (.seq adxBody (.block restore))

end VG.Impl.Bignum.X86_64.MontFn
