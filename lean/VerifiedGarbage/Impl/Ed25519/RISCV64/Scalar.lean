module

public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 on RISC-V: scalars modulo `L`

The PPC64LE functions (`Impl/Ed25519/PPC64LE/Scalar.lean`), on X25519's
RISC-V field code (`Impl/X25519/RISCV64.lean`: eight 32-bit limbs, one to a
word of the working space, whose base stays in `a3`): ARMv7's bit-serial
reduction, the remainder at `SR` doubled, plus the next bit, then `SR - L`
computed at `SD` as `SR + (2^256 - 1 - L) + 1`, whose carry out is 1 exactly
when `SR ≥ L`, and selected with a mask. The bytes are read from the top, at
`t3` (counted by `t4`, the byte in `t5`).

RISC-V faults on a misaligned access and the contracts state no alignment,
so `scratch` is rounded up to a multiple of 8 (`align`), and the inputs and
the result are read and written a byte at a time (`loadLE32`, `storeLE32`).
The functions use only caller-saved registers and no stack: `out` stays in
`a0`, which the field code never writes. Every address is a pointer plus a
constant or a counter, and the only branches are on the counters, so only
the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.X25519.RISCV64 (pass ldSrc storeN cswap prologue zeroAcc row addSrc align)

/-- Where the 16 limbs of a product are. -/
def ACC : Nat := 864
/-- Where the running remainder and its candidate are. -/
def SR : Nat := 160
def SD : Nat := 192

/-! ## Elements to and from bytes -/

/-- The element at `a` as the 32 bytes at `p` plus `dst`, a word at a time. -/
def packField (p : Reg) (a dst : Nat) : List Instr :=
  (List.range 8).flatMap fun k => [.load .w .a4 .a3 (a + 4 * k)] ++ storeLE32 .a4 .a5 p (dst + 4 * k)

/-- The 32 bytes at `p` plus `src` as the element at `o`. -/
def unpackField (p : Reg) (o src : Nat) : List Instr :=
  (List.range 8).flatMap fun k => loadLE32 .a4 .a5 p (src + 4 * k) ++ [.store .w .a4 .a3 (o + 4 * k)]

/-! ## The reduction -/

/-- Word `k` of the complement of `L`, without its final carry-in. -/
def scalarComplement (k : Nat) : Nat := 2 ^ 32 - 1 - Spec.Ed25519.L / 2 ^ (32 * k) % 2 ^ 32

def scalarDoubleSrc (k : Nat) : List Instr := [.load .w .a4 .a3 (SR + 4 * k), .add .a4 .a4 .a4]

/-- Word `k` of `SR` plus that of the complement, which `lui` and `addiw` build
(sign-extended) and two shifts zero-extend. -/
def scalarSubtractSrc (k : Nat) : List Instr :=
  [.load .w .a4 .a3 (SR + 4 * k)] ++ li32 .a2 (BitVec.ofNat 32 (scalarComplement k)) ++
    [.shift .sll .d .a2 .a2 32, .shift .srl .d .a2 .a2 32, .add .a4 .a4 .a2]

/-- Consume bit `j` of `t5`, doubling the remainder and subtracting `L` if
necessary. -/
def scalarBit (j : Nat) : List Instr :=
  [.shift .sll .d .a5 .t5 (63 - j), .shift .srl .d .a5 .a5 63] ++ pass .a3 SR scalarDoubleSrc ++
    [.li .a5 1] ++ pass .a3 SD scalarSubtractSrc ++ [.li .t0 0, .sub .t0 .t0 .a5] ++ cswap SR SD

def scalarRead : List Instr := [.addi .t4 .t4 (-1), .add .a4 .t3 .t4, .load .b .t5 .a4 0]

def scalarByte : List Instr := scalarRead ++ (List.range 8).reverse.flatMap scalarBit

def scalarInit : List Instr := [.li .a4 0] ++ storeN .a4 SR 8 ++ [.li .t4 64]

/-- Reduce the 64-byte integer at `t3`. -/
def scalarReduceEngine : Prog isa :=
  .seq (.block scalarInit) (.loop (.block scalarByte) (.nonzero .t4))

/-! ## `vg_ed25519_scalar_reduce(out = a0, wide = a1, scratch = a2)` -/

def scalarReduceSetup : List Instr := [.addi .a3 .a2 0] ++ align ++ [.addi .t3 .a1 0]

def scalarFinish : List Instr := packField .a0 SR 0

def scalarReduce : Prog isa :=
  .seq (.block scalarReduceSetup) (.seq scalarReduceEngine (.block scalarFinish))

/-! ## `vg_ed25519_scalar_mul_add(out = a0, r = a1, k = a2, s = a3, scratch = a4)` -/

/-- Exact 256-by-256 multiplication, before any modular reduction. -/
def scalarWideMul (x y : Nat) : Prog isa :=
  .seq (.block (prologue ++ zeroAcc ACC ++ [.addi .a6 .a3 0, .li .t0 8]))
    (.loop (.block (row ACC x y)) (.nonzero .t0))

def scalarWideAdd (r : Nat) : List Instr :=
  [.li .a5 0] ++ pass .a3 ACC (addSrc ACC r) ++ pass .a3 (ACC + 32) (ldSrc (ACC + 32))

/-- The 512-bit sum, as bytes 512 to 575 of the working space. -/
def scalarPackWide : List Instr :=
  [.addi .t3 .a3 512] ++ packField .t3 ACC 0 ++ packField .t3 (ACC + 32) 32

def scalarMulAddEngine : Prog isa :=
  .seq (scalarWideMul 96 128) <|
    .seq (.block (scalarWideAdd 64 ++ scalarPackWide)) scalarReduceEngine

def scalarMulAddArgs : List Instr :=
  [.addi .t5 .a3 0, .addi .a3 .a4 0] ++ align ++
    unpackField .a1 64 0 ++ unpackField .a2 96 0 ++ unpackField .t5 128 0

def scalarMulAdd : Prog isa :=
  .seq (.block scalarMulAddArgs) (.seq scalarMulAddEngine (.block scalarFinish))

end VG.Impl.Ed25519.RISCV64
