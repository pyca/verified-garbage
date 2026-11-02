module

public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# Ed25519 on RISC-V: scalars modulo `L`

The functions on X25519's RISC-V field code (`Impl/X25519/RISCV64.lean`:
eight 32-bit limbs, one to a word of the working space, whose base stays in
`a3`): the reduction folds the input in a 64-bit word at a time
(`wordFold`), into a remainder in registers; `vg_ed25519_scalar_mul_add`
multiplies first, into 16 limbs, and reduces the 64 bytes of the result.

RISC-V faults on a misaligned access and the contracts state no alignment,
so `scratch` is rounded up to a multiple of 8 (`align`), and the inputs and
the result are read and written a byte at a time (`loadLE64`, `storeLE32`).
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
/-- Where the remainder is. -/
def SR : Nat := 160

/-! ## Elements to and from bytes -/

/-- The element at `a` as the 32 bytes at `p` plus `dst`, a word at a time. -/
def packField (p : Reg) (a dst : Nat) : List Instr :=
  (List.range 8).flatMap fun k => [.load .w .a4 .a3 (a + 4 * k)] ++ storeLE32 .a4 .a5 p (dst + 4 * k)

/-- The 32 bytes at `p` plus `src` as the element at `o`. -/
def unpackField (p : Reg) (o src : Nat) : List Instr :=
  (List.range 8).flatMap fun k => loadLE32 .a4 .a5 p (src + 4 * k) ++ [.store .w .a4 .a3 (o + 4 * k)]

/-! ## The reduction

Division by the constant subgroup order `L = 2^252 + c` (`c < 2^125`), a
64-bit word at a time, from the top, as on x86-64 and AArch64
(`Impl/Ed25519/X86_64/Scalar.lean`): the remainder `r < L` (in `a4`–`a7`)
becomes `v = 2^64 r + w` for the next word `w`, which is `h 2^252 + l` with
`h < 2^65`, and `v ≡ l + L - h c` (mod L) since `2^252 ≡ -c`. With `t = h c
< L`, that is `l - t` when `t ≤ l` (below `2^252 < L`) and `l + L - t`
otherwise (below `L`): the four-word difference `l - t`, plus `L` under the
mask of its borrow, is `v mod L` (`wordFold`). RISC-V has no carry flag:
each carry or borrow is an `sltu` of a sum or of the two operands. The two
low words of `c` stay in `t5` and `t6`. -/

/-- The low and high words of `c = L - 2^252`. -/
def orderLo : BitVec 64 := 0x5812631a5cf5d3ed
def orderHi : BitVec 64 := 0x14def9dea2f79cd6

/-- The next word, from the top (`t4` counts its bytes down from 64), into `a2`. -/
def scalarLoad : List Instr := [.addi .t4 .t4 (-8), .add .a1 .t3 .t4] ++ loadLE64 .a2 .t0 .t1 .a1 0

/-- From `r = (r₀, r₁, r₂, r₃)` in `a4`–`a7` and `w` in `a2`: `h₀ = r₂ >> 60 | 2^4 r₃`
(`t0`) and `h₁ = r₃ >> 60` (`t1`), so that `h₀ + 2^64 h₁ = (2^64 r + w) >> 252`; and
`l = (w, r₀, r₁, r₂ mod 2^60)` into `a4`–`a7`. -/
def foldPrep : List Instr :=
  [.shift .srl .d .t0 .a6 60, .shift .sll .d .t1 .a7 4, .logic .or .t0 .t0 .t1,
    .shift .srl .d .t1 .a7 60, .shift .sll .d .a7 .a6 4, .shift .srl .d .a7 .a7 4,
    .addi .a6 .a5 0, .addi .a5 .a4 0, .addi .a4 .a2 0]

/-- `t = h₀ c + 2^64 h₁ c`, below `2^190`, into `t2`, `a1`, `t0`. -/
def foldMul : List Instr :=
  [.mul .t2 .t0 .t5, .mulhu .a1 .t0 .t5, .mul .a2 .t0 .t6, .mulhu .t0 .t0 .t6,
    .add .a1 .a1 .a2, .sltu .a2 .a1 .a2, .add .t0 .t0 .a2,
    .mul .a2 .t1 .t5, .add .a1 .a1 .a2, .sltu .a2 .a1 .a2, .add .t0 .t0 .a2,
    .mul .a2 .t1 .t6, .add .t0 .t0 .a2]

/-- Word `k` of `l - t` with the borrow in `a2`: the new borrow into `a2`. -/
def subBorrow (r x : Reg) : List Instr :=
  [.sltu .t1 r x, .sub r r x, .sltu .t2 r .a2, .sub r r .a2, .logic .or .a2 .t1 .t2]

/-- `l - t` into `a4`–`a7`, its borrow into `t1`. -/
def foldSub : List Instr :=
  [.sltu .a2 .a4 .t2, .sub .a4 .a4 .t2] ++ subBorrow .a5 .a1 ++ subBorrow .a6 .t0 ++
    [.sltu .t1 .a7 .a2, .sub .a7 .a7 .a2]

/-- `L` added to `a4`–`a7` under the mask of the borrow in `t1`. -/
def foldAdd : List Instr :=
  [.li .t2 0, .sub .t2 .t2 .t1,
    .logic .and .a1 .t5 .t2, .add .a4 .a4 .a1, .sltu .a1 .a4 .a1,
    .logic .and .a2 .t6 .t2, .add .a5 .a5 .a1, .sltu .a1 .a5 .a1, .add .a5 .a5 .a2,
    .sltu .a2 .a5 .a2, .logic .or .a1 .a1 .a2,
    .add .a6 .a6 .a1, .sltu .a1 .a6 .a1, .add .a7 .a7 .a1,
    .shift .sll .d .t1 .t1 60, .add .a7 .a7 .t1]

/-- From the remainder `r < L` in `a4`–`a7` and the next word `w` in `a2`: `v mod L`
for `v = 2^64 r + w`, into `a4`–`a7`. -/
def wordFold : List Instr := foldPrep ++ foldMul ++ foldSub ++ foldAdd

def scalarWord : List Instr := scalarLoad ++ wordFold

def scalarInit : List Instr :=
  [.li .a4 0, .li .a5 0, .li .a6 0, .li .a7 0, .li .t4 64] ++
    li64 .t5 .t0 orderLo ++ li64 .t6 .t0 orderHi

/-- The remainder, into `SR`. -/
def scalarStore : List Instr :=
  [.store .d .a4 .a3 SR, .store .d .a5 .a3 (SR + 8), .store .d .a6 .a3 (SR + 16),
    .store .d .a7 .a3 (SR + 24)]

/-- Reduce the 64-byte integer at `t3`, into `SR`. -/
def scalarReduceEngine : Prog isa :=
  .seq (.block scalarInit) (.seq (.loop (.block scalarWord) (.nonzero .t4)) (.block scalarStore))

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
