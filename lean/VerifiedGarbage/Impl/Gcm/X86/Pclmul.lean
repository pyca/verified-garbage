module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# GHASH with PCLMULQDQ on x86 (32-bit)

`vg_ghash_pclmul(h, y, data, n, scratch)`, with the contract of `vg_ghash`
(`Proof.Gcm.ghashX86`), for CPUs with PCLMULQDQ and SSSE3 (for `pshufb`).
The reflected field arithmetic is that of the x86-64 implementation
(`Impl/Gcm/X86_64/Pclmul.lean`): the product of two registers, reduced
(`zero`, `acc`, `reduce`), is `x · a · b`, and the hash subkey is used as
`H' = H · x⁻¹`.

With eight blocks or more, `H'¹`, …, `H'⁸` are computed once per call into
`scratch` (`H'ᵏ⁺¹` at `scratch + 16 k`, `pows`), since eight registers
cannot hold them, and eight blocks at a time
`Y ← mul(Y ⊕ X₁, H'⁸) ⊕ mul(X₂, H'⁷) ⊕ … ⊕ mul(X₈, H')`, reducing the sum of
the eight products once (`body8`). A block's product there is three
carry-less multiplications (`kblock`): of the low halves, of the high
halves, and of the sums of the halves, whose sum with the two others is the
middle of the product, added once for the eight (`kreduce`); the sum of a
power's halves is in `scratch` too, two powers to a slot (the slots 10 to
13, `halves`), and so is the reduction's constant (the slot 9), which the
blocks leave no register for. `Y` is kept in the slot 8 between the turns,
and its block is the last a turn multiplies. The remaining blocks go one at
a time, with `H'` alone, which is all that fewer than eight blocks compute:
they do not write `scratch`.

All GPR writes are caller-saved (`eax`, `ecx`, `edx`), so stack use is zero.
Every branch and every address depends only on the pointers and `n`.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86.Pclmul
open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def argOp (i : Nat) : MemOp := at_ .esp (4 + 4 * i)
def revMask : BitVec 128 := 0x000102030405060708090a0b0c0d0e0f#128
def poly : BitVec 128 := 0xc2000000000000000000000000000000#128
def xInv : BitVec 128 := 0xc2000000000000000000000000000001#128

/-- Build a constant in registers; xmm5 is free during setup. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  ([.mov .eax (.imm (c.extractLsb' 96 32)), .xop (.movd x .eax)] : List Instr) ++
  (List.range 3).flatMap (fun k =>
    [.xop (.shift .pslldq x 4), .mov .eax (.imm (c.extractLsb' (32 * (2 - k)) 32)),
     .xop (.movd .xmm5 .eax), .xop (.bin .por x .xmm5)])

/-! xmm0 reversal, xmm1 polynomial, xmm2 Y/input, xmm3 H*x^-1, xmm4 lo,
xmm5 mid, xmm6 hi, xmm7 temporary; in a block of eight, xmm1 is the sum of
the block's halves and xmm3 a power and then the sums of its halves. -/

def zero : List Instr :=
  [.xop (.bin .pxor .xmm4 .xmm4), .xop (.bin .pxor .xmm5 .xmm5),
   .xop (.bin .pxor .xmm6 .xmm6)]

/-- The product of `xmm2` and `xmm3` into `xmm4` (lo), `xmm5` (mid) and
`xmm6` (hi): three of its four carry-less multiplications each in a copy of
`xmm2` made in the register it is left in, the fourth in `xmm2` itself. -/
def mul4 : List Instr :=
  [.xop (.bin .movdqa .xmm4 .xmm2), .xop (.pclmulqdq .xmm4 .xmm3 0x00),
   .xop (.bin .movdqa .xmm6 .xmm2), .xop (.pclmulqdq .xmm6 .xmm3 0x11),
   .xop (.bin .movdqa .xmm5 .xmm2), .xop (.pclmulqdq .xmm5 .xmm3 0x01),
   .xop (.pclmulqdq .xmm2 .xmm3 0x10), .xop (.bin .pxor .xmm5 .xmm2)]

def fold : List Instr :=
  [.xop (.bin .movdqa .xmm7 .xmm4), .xop (.pclmulqdq .xmm7 .xmm1 0x10),
   .xop (.pshufd .xmm4 .xmm4 0x4e), .xop (.bin .pxor .xmm4 .xmm7)]

def reduce : List Instr :=
  ([.xop (.bin .movdqa .xmm7 .xmm5), .xop (.shift .psrldq .xmm7 8),
   .xop (.bin .pxor .xmm6 .xmm7), .xop (.shift .pslldq .xmm5 8),
   .xop (.bin .pxor .xmm4 .xmm5)] : List Instr) ++ fold ++ fold ++
  ([.xop (.bin .movdqa .xmm2 .xmm6), .xop (.bin .pxor .xmm2 .xmm4)] : List Instr)

/-- H arrives in xmm7; xmm4/xmm5/xmm6 are available during setup. -/
def hInv : List Instr :=
  const .xmm4 xInv ++
  ([.mov .eax (.imm 0xffffffff), .xop (.movd .xmm5 .eax),
   .xop (.bin .punpckldq .xmm5 .xmm5), .xop (.bin .punpcklqdq .xmm5 .xmm5),
   .xop (.bin .movdqa .xmm3 .xmm7), .xop (.shift .psllq .xmm3 1),
   .xop (.bin .movdqa .xmm6 .xmm7), .xop (.shift .psrlq .xmm6 63),
   .xop (.shift .pslldq .xmm6 8), .xop (.bin .por .xmm3 .xmm6),
   .xop (.pshufd .xmm6 .xmm7 0xff), .xop (.shift .psrld .xmm6 31),
   .xop (.bin .paddd .xmm6 .xmm5), .xop (.bin .pandn .xmm6 .xmm4),
   .xop (.bin .pxor .xmm3 .xmm6)] : List Instr)

/-- The constants, `H'` into `xmm3`, `Y` into `xmm2`, the data in `edx`, the
number of blocks in `eax`, and `cmp eax, 8`. -/
def prologue : List Instr :=
  const .xmm0 revMask ++ const .xmm1 poly ++
  ([.mov .eax (.mem (argOp 0)), .movdquLoad .xmm7 (at_ .eax 0),
   .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++ hInv ++
  ([.mov .ecx (.mem (argOp 1)), .movdquLoad .xmm2 (at_ .ecx 0),
   .xop (.bin .pshufb .xmm2 .xmm0), .mov .edx (.mem (argOp 2)),
   .mov .eax (.mem (argOp 3)), .alu .cmp .eax (.imm 8)] : List Instr)

/-- The 16 bytes at `scratch + 16 k`, with `scratch` in `ecx`. -/
def slot (k : Nat) : MemOp := at_ .ecx (16 * k)

/-- The product of the slots `a` and `b`, reduced, into the slot `d`. -/
def mulSlots (d a b : Nat) : List Instr :=
  ([.movdquLoad .xmm2 (slot a), .movdquLoad .xmm3 (slot b)] : List Instr) ++ mul4 ++ reduce ++
  ([.movdquStore (slot d) .xmm2] : List Instr)

/-- For the powers in the slots `2 k` and `2 k + 1`: the sum of the halves
of the first in the low quadword of the slot `10 + k`, and of the second in
its high quadword. -/
def halves (k : Nat) : List Instr :=
  [.movdquLoad .xmm2 (slot (2 * k)), .movdquLoad .xmm3 (slot (2 * k + 1)),
   .xop (.pshufd .xmm4 .xmm2 0x4e), .xop (.bin .pxor .xmm4 .xmm2),
   .xop (.pshufd .xmm5 .xmm3 0x4e), .xop (.bin .pxor .xmm5 .xmm3),
   .xop (.bin .punpcklqdq .xmm4 .xmm5), .movdquStore (slot (10 + k)) .xmm4]

/-- `scratch` into `ecx`; `Y` into the slot 8 and the reduction's constant
into the slot 9; `H'ᵏ⁺¹` into the slot `k`, for `k < 8`, each the product of
two powers before it; and the sums of their halves into the slots 10 to
13. -/
def pows : List Instr :=
  ([.mov .ecx (.mem (argOp 4)), .movdquStore (slot 8) .xmm2, .movdquStore (slot 0) .xmm3,
    .movdquStore (slot 9) .xmm1] : List Instr) ++
  mulSlots 1 0 0 ++ mulSlots 2 1 0 ++ mulSlots 3 1 1 ++ mulSlots 4 2 1 ++ mulSlots 5 2 2 ++
  mulSlots 6 3 2 ++ mulSlots 7 3 3 ++ halves 0 ++ halves 1 ++ halves 2 ++ halves 3

/-- Which quadword of its slot holds the sum of the halves of the power in
the slot `k`. -/
def halfSel (k : Nat) : BitVec 8 := if k % 2 = 0 then 0x00 else 0x10

/-- The block in `xmm2` times the power in the slot `k`, added to `xmm4`
(the product of the low halves, in a copy of the block in `xmm7`), `xmm6`
(of the high halves, in `xmm2` itself) and `xmm5` (of the sums of the
halves: the block's in `xmm1`, the power's loaded from the slot
`10 + k / 2`). -/
def kblock (k : Nat) : List Instr :=
  [.movdquLoad .xmm3 (slot k),
   .xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x00), .xop (.bin .pxor .xmm4 .xmm7),
   .xop (.pshufd .xmm1 .xmm2 0x4e), .xop (.bin .pxor .xmm1 .xmm2),
   .xop (.pclmulqdq .xmm2 .xmm3 0x11), .xop (.bin .pxor .xmm6 .xmm2),
   .movdquLoad .xmm3 (slot (10 + k / 2)),
   .xop (.pclmulqdq .xmm1 .xmm3 (halfSel k)), .xop (.bin .pxor .xmm5 .xmm1)]

/-- Block `j` of eight, `0 < j`: the product of `Xⱼ₊₁` and `H'⁸⁻ʲ`, added. -/
def later (j : Nat) : List Instr :=
  ([.movdquLoad .xmm2 (at_ .edx (16 * j)), .xop (.bin .pshufb .xmm2 .xmm0)] : List Instr) ++ kblock (7 - j)

/-- The first block of eight, which is multiplied last: the product of
`Y ⊕ X₁` and `H'⁸`, added, with `Y` from the slot 8. -/
def last : List Instr :=
  ([.movdquLoad .xmm2 (at_ .edx 0), .xop (.bin .pshufb .xmm2 .xmm0), .movdquLoad .xmm3 (slot 8),
   .xop (.bin .pxor .xmm2 .xmm3)] : List Instr) ++ kblock 7

/-- A step of the reduction, with `xmm5` for its product. -/
def kfold : List Instr :=
  [.xop (.bin .movdqa .xmm5 .xmm4), .xop (.pclmulqdq .xmm5 .xmm1 0x10),
   .xop (.pshufd .xmm4 .xmm4 0x4e), .xop (.bin .pxor .xmm4 .xmm5)]

/-- After the eight blocks: the middle of the product (the products of the
sums of the halves, plus the two others), the reduction with its constant
loaded from the slot 9, and `Y` left in `xmm6` and stored in the slot 8:
none of the registers the blocks load into holds a result of it. -/
def kreduce : List Instr :=
  ([.xop (.bin .pxor .xmm5 .xmm4), .xop (.bin .pxor .xmm5 .xmm6),
   .xop (.bin .movdqa .xmm7 .xmm5), .xop (.shift .psrldq .xmm7 8),
   .xop (.bin .pxor .xmm6 .xmm7), .xop (.shift .pslldq .xmm5 8),
   .xop (.bin .pxor .xmm4 .xmm5), .movdquLoad .xmm1 (slot 9)] : List Instr) ++ kfold ++ kfold ++
  ([.xop (.bin .pxor .xmm6 .xmm4), .movdquStore (slot 8) .xmm6] : List Instr)

/-- Eight blocks, with `scratch` in `ecx` and `Y` in the slot 8, where it
leaves it (and in `xmm6`). -/
def body8 : List Instr :=
  zero ++ later 1 ++ later 2 ++ later 3 ++ later 4 ++ later 5 ++ later 6 ++ later 7 ++ last ++ kreduce ++
  ([.alu .add .edx (.imm 128), .alu .sub .eax (.imm 8), .alu .cmp .eax (.imm 8)] : List Instr)

def body : List Instr :=
  ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
   .xop (.bin .pxor .xmm2 .xmm7)] : List Instr) ++ mul4 ++ reduce ++
  ([.alu .add .edx (.imm 16), .alu .sub .eax (.imm 1)] : List Instr)

def epilogue : List Instr :=
  [.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .ecx 0) .xmm2]

/-- After the blocks of eight: `Y` into `xmm2`, `H'` into `xmm3`, and `y`
back into `ecx`. -/
def after8 : List Instr :=
  [.xop (.bin .movdqa .xmm2 .xmm6), .movdquLoad .xmm3 (slot 0), .mov .ecx (.mem (argOp 1))]

/-- After `cmp eax, 8`: unless there are fewer than eight blocks, the
powers, the blocks eight at a time, and `after8`; then the blocks left one
at a time, and `Y` stored. -/
def ghash : Prog isa :=
  .seq (.block prologue)
    (.seq (.ite .b (.block [])
        (.seq (.block pows) (.seq (.loop (.block body8) .ae) (.block after8))))
      (.seq (.block [.alu .test .eax (.reg .eax)])
        (.seq (.ite .e (.block []) (.loop (.block body) .ne)) (.block epilogue))))

end VG.Impl.Gcm.X86.Pclmul
