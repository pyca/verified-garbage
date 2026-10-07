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
words 16–19 in `xmm3` and `xmm4` first and writes them back before it
returns, so that it changes only `aAcc`, `aTmp` and `o`. Squares (`a = b`,
which the indices tell, and so publicly) take the triangular tiles.

As `vg_rsa_mont_mul`, it uses no stack and keeps `rbx`, `rbp` and `r12`–`r15`
in `xmm0`–`xmm2` while it runs.
-/

namespace VG.Impl.Bignum.X86_64.MontFn

open VG.X86_64 VG.Impl.Bignum.X86_64.Public

/-- The indices whose header slots get the bases of `o`, `a` and `b`. -/
def xO : Nat := 8
def xA : Nat := 9
def xB : Nat := 10

/-- Header words 16–19 into `xmm3` and `xmm4`, and the bases of the arrays in
`edx`, `ecx` and `r8d` into the slots of `xO`, `xA` and `xB`. -/
def slotsIn : List Instr :=
  [.movdquLoad .xmm3 (hdr (sArr xO)), .movdquLoad .xmm4 (hdr (sArr xB)),
    .mov .rax (.mem (arrAt .rdx)), .store (hdr (sArr xO)) .rax,
    .mov .rax (.mem (arrAt .rcx)), .store (hdr (sArr xA)) .rax,
    .mov .rax (.mem (arrAt .r8)), .store (hdr (sArr xB)) .rax]

/-- The bases of the accumulator and the temporary for `leave`, and header
words 16–19 back. -/
def slotsOut : List Instr :=
  [.mov .r8 (.mem (hdr (sArr aAcc))), .mov .rsi (.mem (hdr (sArr aTmp))),
    .movdquStore (hdr (sArr xO)) .xmm3, .movdquStore (hdr (sArr xB)) .xmm4]

/-- The tiles: the square's if `a = b`, the product's otherwise. -/
def tiled : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.reg .r8)])
    (.ite .e (AdxTiledSquare.montSquare xO xA) (AdxTiledProduct.montMul xO xA xB))

/-- The tiles for `w` a multiple of 8, `montMul` otherwise. -/
def adxBody : Prog isa :=
  .seq (.block AdxSquare.redcTest)
    (.ite .e tiled (.seq (.block basesR) (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))))

/-- `vg_rsa_mont_mul_adx`. -/
def mulAdx : Prog isa :=
  .seq (.block (enter ++ slotsIn)) (.seq adxBody (.seq (.block slotsOut) (.block leave)))

end VG.Impl.Bignum.X86_64.MontFn
