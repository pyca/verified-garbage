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
`Y ← mul(Y ⊕ X₁, H'⁸) ⊕ mul(X₂, H'⁷) ⊕ … ⊕ mul(X₈, H')`, each block's
power loaded into `xmm3`, reducing the sum of the eight products once
(`body8`). The remaining blocks go one at a time, with `H'` alone, which is
all that fewer than eight blocks compute: they do not write `scratch`.

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

/-! xmm0 reversal, xmm1 polynomial, xmm2 Y/input, xmm3 H*x^-1 (a power of
it, for a block of eight), xmm4 lo, xmm5 mid, xmm6 hi, xmm7 temporary. -/

def zero : List Instr :=
  [.xop (.bin .pxor .xmm4 .xmm4), .xop (.bin .pxor .xmm5 .xmm5),
   .xop (.bin .pxor .xmm6 .xmm6)]

def acc : List Instr :=
  [.xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x00),
   .xop (.bin .pxor .xmm4 .xmm7),
   .xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x11),
   .xop (.bin .pxor .xmm6 .xmm7),
   .xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x01),
   .xop (.bin .pxor .xmm5 .xmm7),
   .xop (.bin .movdqa .xmm7 .xmm2), .xop (.pclmulqdq .xmm7 .xmm3 0x10),
   .xop (.bin .pxor .xmm5 .xmm7)]

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
  ([.movdquLoad .xmm2 (slot a), .movdquLoad .xmm3 (slot b)] : List Instr) ++ zero ++ acc ++ reduce ++
  ([.movdquStore (slot d) .xmm2] : List Instr)

/-- `scratch` into `ecx`, and `H'ᵏ⁺¹` into the slot `k`, for `k < 8`, each
the product of two powers before it; `Y` is kept in the slot 8 meanwhile. -/
def pows : List Instr :=
  ([.mov .ecx (.mem (argOp 4)), .movdquStore (slot 8) .xmm2, .movdquStore (slot 0) .xmm3] : List Instr) ++
  mulSlots 1 0 0 ++ mulSlots 2 1 0 ++ mulSlots 3 1 1 ++ mulSlots 4 2 1 ++ mulSlots 5 2 2 ++
  mulSlots 6 3 2 ++ mulSlots 7 3 3 ++ ([.movdquLoad .xmm2 (slot 8)] : List Instr)

/-- The first block of eight: the product of `Y ⊕ X₁` and `H'⁸`. -/
def first : List Instr :=
  ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
   .xop (.bin .pxor .xmm2 .xmm7), .movdquLoad .xmm3 (slot 7)] : List Instr) ++ zero ++ acc

/-- Block `j` of eight, `0 < j`: the product of `Xⱼ₊₁` and `H'⁸⁻ʲ`, added. -/
def next (j : Nat) : List Instr :=
  ([.movdquLoad .xmm2 (at_ .edx (16 * j)), .xop (.bin .pshufb .xmm2 .xmm0),
   .movdquLoad .xmm3 (slot (7 - j))] : List Instr) ++ acc

/-- Eight blocks, with `scratch` in `ecx`; it leaves `H'` in `xmm3`. -/
def body8 : List Instr :=
  first ++ next 1 ++ next 2 ++ next 3 ++ next 4 ++ next 5 ++ next 6 ++ next 7 ++ reduce ++
  ([.alu .add .edx (.imm 128), .alu .sub .eax (.imm 8), .alu .cmp .eax (.imm 8)] : List Instr)

def body : List Instr :=
  ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
   .xop (.bin .pxor .xmm2 .xmm7)] : List Instr) ++ zero ++ acc ++ reduce ++
  ([.alu .add .edx (.imm 16), .alu .sub .eax (.imm 1)] : List Instr)

def epilogue : List Instr :=
  [.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .ecx 0) .xmm2]

/-- After `cmp eax, 8`: unless there are fewer than eight blocks, the
powers, the blocks eight at a time, and `y` back into `ecx`; then the blocks
left one at a time, and `Y` stored. -/
def ghash : Prog isa :=
  .seq (.block prologue)
    (.seq (.ite .b (.block [])
        (.seq (.block pows) (.seq (.loop (.block body8) .ae) (.block [.mov .ecx (.mem (argOp 1))]))))
      (.seq (.block [.alu .test .eax (.reg .eax)])
        (.seq (.ite .e (.block []) (.loop (.block body) .ne)) (.block epilogue))))

end VG.Impl.Gcm.X86.Pclmul
