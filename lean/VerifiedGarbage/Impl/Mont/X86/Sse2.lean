module

public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Impl.Mont.X86.MulRt

/-! # Montgomery multiplication with SSE2 `pmuludq` (32-bit x86)

One kernel for `vg_rsa_mont_mul_at` and `vg_rsa_mont_mul`, whose code differs
only in how it finds its numbers (`atParams`, `preparedParams`): the
product `A B R⁻¹ mod M` of numbers of `N` 32-bit words, `R = 2^(32 N)`, by
product scanning. Column `k` adds the products `A_i B_(k-i)` (for a square,
the products with `i < k - i` doubled and the diagonal) and `Q_j M_(k-j)`
for the quotient digits `Q_j` of the earlier columns, two at a time with
`pmuludq` on pairs of words read straight from the numbers (`pair`), then
the column's own digit `Q_k = Z (-M⁻¹) mod 2³²` while `k < N`, which
clears the column's low word, or else the column's word of the result.

The SSE2 lanes add the 64-bit products modulo `2⁶⁴` (`xmm0`) and their
high words exactly (`xmm1`), which are both enough and cheaper than
splitting every product: for the sum `L` of the products' low words and the
incoming carry `c`, the column is `2³² H + L + c` with `L + c < 2⁶⁴`, and
`Z = (S + c) mod 2⁶⁴` has the low word of `L + c` and the high word `H_lo +
(L + c)_hi mod 2³²`, so the outgoing carry is `H + (L + c)_hi`: its low word
`Z_hi` and its high word `H_hi + [Z_hi < H_lo]`.

The working area, at the scratch pointer `S`: the column's sums (`S + 0`,
`S + 8`) and the carry (`S + 16`), then `2 N + 1` words from `S + 24`: the
quotient digits, the result's `N` words and its top word. The result, below
`2 M`, is reduced by one subtraction of `M` into the digits' words, then
selected into `O` by a mask, by the run-time width multiplication's loops.

The callee-saved registers are in a frame of 16 bytes, the seven public
parameters (`prm`) in a frame of 28 bytes, and the columns run in an MCDT
frame (`TCB/X86/Isa.lean`), as `pmuludq` must. Every branch and address
depends only on the parameters and the column, so the timing does not
depend on the numbers.
-/

@[expose] public section

namespace VG.Impl.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- The parameters, in the frame of 28 bytes at `esp + d`: `A` (0), `B` (1),
`M` (2), `O` (3), the scratch pointer (4), the pointer to `-M⁻¹ mod 2³²`
(5) and `4 N` (6). -/
def prm (d i : Nat) : MemOp := at_ .esp (d + 4 * i)

/-- The parameters inside the MCDT frame, 12 bytes further down. -/
def kp (i : Nat) : MemOp := prm 12 i

def pA : Nat := 0
def pB : Nat := 1
def pM : Nat := 2
def pO : Nat := 3
def pS : Nat := 4
def pInv : Nat := 5
def pN4 : Nat := 6

/-- The scratch offsets: the column's sum, its high sum, the carry, and the words. -/
def offS : Nat := 0
def offH : Nat := 8
def offC : Nat := 16
def offW : Nat := 24

/-! ## Products -/

/-- `xmm0 += x`, `xmm1 += x >> 32` (in both lanes); `x` changes. -/
def acc (x : XReg) : List Instr :=
  [.xop (.bin .paddq .xmm0 x), .xop (.shift .psrlq x 32), .xop (.bin .paddq .xmm1 x)]

/-- The products `X_i Y_(k-i)` and `X_(i+1) Y_(k-i-1)`, for `esi` at `X_i`
plus `dx` and `edi` at `Y_(k-i-1)` plus `dy`: `movq` reads two words,
`pshufd` puts them in doublewords 0 and 2 (`Y`'s swapped), `pmuludq`
multiplies each pair. -/
def pair (dx dy : Nat) : List Instr :=
  [.movqLoad .xmm2 (at_ .esi dx), .xop (.pshufd .xmm2 .xmm2 0x10),
    .movqLoad .xmm3 (at_ .edi dy), .xop (.pshufd .xmm3 .xmm3 0x01),
    .pmuludq .xmm2 .xmm3] ++ acc .xmm2

/-- Four products: two pairs (`edi` at `Y_(k-i-3)`), `esi` up 16 bytes, `edi`
down 16 and the count of bytes left, `ebp`, down 16; CF clear if another four
remain. -/
def quadBody : List Instr :=
  pair 0 8 ++ pair 8 0 ++ [.alu .add .esi (.imm 16), .alu .sub .edi (.imm 16),
    .alu .sub .ebp (.imm 16), .alu .cmp .ebp (.imm 16)]

/-- `X_i Y_(k-i)` alone, `esi` at `X_i` and `edi + 4` at `Y_(k-i)`. -/
def single : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .xop (.movd .xmm2 .eax),
    .mov .eax (.mem (at_ .edi 4)), .xop (.movd .xmm3 .eax),
    .pmuludq .xmm2 .xmm3] ++ acc .xmm2

/-- `Σ X_i Y_(k-i)` for `i0 ≤ i < e` (none if `e ≤ i0`), into the sums:
`esi = X`, `edi = Y`, `ecx = 4 k`, `edx = 4 i0` and `ebx = 4 e` on entry.
`ebp` counts the bytes of `X` left, `4 (e - i)`; four products at a time,
then two, then one. `edi` is at `Y_(k-i-3)` for the current `i`, below `Y`
when `k - i < 3`; it is only read then at a displacement that reaches `Y`'s
words. Only the count, not a pointer, controls the loops. Uses `eax`, `esi`,
`edi` and `ebp`. -/
def dot : Prog isa := seqs [
  .block [.mov .ebp (.reg .ebx), .alu .sub .ebp (.reg .edx)],
  .ite .b (.block [.mov .ebp (.imm 0)]) (.block []),
  .block [.alu .add .esi (.reg .edx), .alu .add .edi (.reg .ecx), .alu .sub .edi (.reg .edx),
    .alu .sub .edi (.imm 12), .alu .cmp .ebp (.imm 16)],
  .ite .ae (.loop (.block quadBody) .ae) (.block []),
  .block [.alu .cmp .ebp (.imm 8)],
  .ite .ae (.block (pair 0 8 ++ [.alu .add .esi (.imm 8), .alu .sub .edi (.imm 8), .alu .sub .ebp (.imm 8)]))
    (.block []),
  .block [.alu .add .edi (.imm 8), .alu .cmp .ebp (.imm 4)],
  .ite .ae (.block single) (.block [])]

/-- A parameter's value into `r`. -/
def ld (i : Nat) (r : Reg) : List Instr := [.mov r (.mem (kp i))]

/-- The quotient digits' address, `S + 24`, into `r`. -/
def ldQ (r : Reg) : List Instr := [.mov r (.mem (kp pS)), .alu .add r (.imm (BitVec.ofNat 32 offW))]

/-! ## A column -/

/-- `edx = 4 i0 = max(0, 4 k + 4 - 4 N)`; `eax` changes. Public values are
loaded by `mov` before an operation takes them, which keeps them public for
the taint analysis. -/
def lowIdx : Prog isa := .seq
  (.block [.mov .eax (.mem (kp pN4)), .mov .edx (.reg .ecx), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)])
  (.ite .b (.block [.mov .edx (.imm 0)]) (.block []))

/-- `ebx = min(4 k + 4, 4 N)`; `eax` changes. -/
def endProduct : Prog isa := .seq
  (.block [.mov .eax (.mem (kp pN4)), .mov .ebx (.reg .ecx), .alu .add .ebx (.imm 4), .alu .cmp .ebx (.reg .eax)])
  (.ite .ae (.block [.mov .ebx (.reg .eax)]) (.block []))

/-- `ebx = 4 ⌊(k + 1) / 2⌋`, the products with `i < k - i`. -/
def endHalf : List Instr :=
  [.mov .ebx (.reg .ecx), .alu .add .ebx (.imm 4), .shift .shr .ebx 3, .alu .add .ebx (.reg .ebx),
    .alu .add .ebx (.reg .ebx)]

/-- `ebx = min(4 k, 4 N)`, the digits before column `k`; `eax` changes. -/
def endReduce : Prog isa := .seq
  (.block [.mov .eax (.mem (kp pN4)), .mov .ebx (.reg .ecx), .alu .cmp .ebx (.reg .eax)])
  (.ite .ae (.block [.mov .ebx (.reg .eax)]) (.block []))

/-- For even `k`, `A_(k/2)²`: `ebx = 4 ⌊(k + 1) / 2⌋` from `endHalf` is
`2 k` exactly when `k` is even, and then the diagonal's offset. -/
def diag : Prog isa := .seq
  (.block [.mov .eax (.reg .ebx), .alu .add .eax (.reg .eax), .alu .cmp .eax (.reg .ecx)])
  (.ite .e (.block ([.mov .esi (.mem (kp pA)), .alu .add .esi (.reg .ebx),
      .mov .eax (.mem (at_ .esi 0)), .xop (.movd .xmm2 .eax), .pmuludq .xmm2 .xmm2] ++ acc .xmm2))
    (.block []))

/-- The products of `A` and `B`: for a square (`A = B`), the products with
`i < k - i`, doubled, and the diagonal. -/
def input : Prog isa := .seq
  (.block [.mov .eax (.mem (kp pA)), .mov .ebx (.mem (kp pB)), .alu .cmp .eax (.reg .ebx)])
  (.ite .e
    (seqs [.block (endHalf ++ ld pA .esi ++ ld pA .edi), dot,
      .block [.xop (.bin .paddq .xmm0 .xmm0), .xop (.bin .paddq .xmm1 .xmm1)], diag])
    (.seq endProduct (.seq (.block (ld pA .esi ++ ld pB .edi)) dot)))

/-- The products of the quotient digits and `M`. -/
def reduce : Prog isa := .seq endReduce (.seq (.block (ldQ .esi ++ ld pM .edi)) dot)

/-- The lanes added into lane 0, the sums stored, and `Z = S + c`: `eax`
its low word, `edx` its high word; `ebx` the scratch pointer. -/
def fold : List Instr :=
  [.xop (.bin .movdqa .xmm2 .xmm0), .xop (.shift .psrldq .xmm2 8), .xop (.bin .paddq .xmm0 .xmm2),
    .xop (.bin .movdqa .xmm2 .xmm1), .xop (.shift .psrldq .xmm2 8), .xop (.bin .paddq .xmm1 .xmm2),
    .mov .ebx (.mem (kp pS)), .movqStore (at_ .ebx offS) .xmm0, .movqStore (at_ .ebx offH) .xmm1,
    .mov .eax (.mem (at_ .ebx offS)), .alu .add .eax (.mem (at_ .ebx offC)),
    .mov .edx (.mem (at_ .ebx (offS + 4))), .alu .adc .edx (.mem (at_ .ebx (offC + 4)))]

/-- `k < N`: the digit `q = Z_lo (-M⁻¹) mod 2³²` stored at word `k`, and
`q M_0` added to `Z` (whose low word becomes zero; `edx` its high word) and
its high word to `H`. -/
def digit : List Instr :=
  [.mov .esi (.reg .edx), .mov .edi (.reg .eax),
    .mov .edx (.mem (kp pInv)), .mov .edx (.mem (at_ .edx 0)), .mul .edx,
    .mov .edx (.reg .ebx), .alu .add .edx (.reg .ecx), .store (at_ .edx offW) .eax,
    .mov .edx (.mem (kp pM)), .mov .edx (.mem (at_ .edx 0)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .adc .esi (.reg .edx),
    .mov .eax (.mem (at_ .ebx offH)), .alu .add .eax (.reg .edx), .store (at_ .ebx offH) .eax,
    .mov .eax (.mem (at_ .ebx (offH + 4))), .alu .adc .eax (.imm 0), .store (at_ .ebx (offH + 4)) .eax,
    .mov .edx (.reg .esi)]

/-- `k ≥ N`: the result's word `Z_lo` stored at word `k`. -/
def word : List Instr :=
  [.mov .esi (.reg .ebx), .alu .add .esi (.reg .ecx), .store (at_ .esi offW) .eax]

/-- The carry `H + (L + c)_hi`: its low word `Z_hi` (`edx`), its high word
`H_hi + [Z_hi < H_lo]`. -/
def carry : List Instr :=
  [.store (at_ .ebx offC) .edx, .alu .cmp .edx (.mem (at_ .ebx offH)),
    .mov .eax (.mem (at_ .ebx (offH + 4))), .alu .adc .eax (.imm 0), .store (at_ .ebx (offC + 4)) .eax]

/-- Column `k` (`ecx = 4 k`), then `ecx` up a word; ZF after the last, `k = 2 N - 1`. -/
def column : Prog isa := seqs [
  .block [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)],
  lowIdx, input, reduce, .block fold,
  .seq (.block [.mov .ebp (.mem (kp pN4)), .alu .cmp .ecx (.reg .ebp)]) (.ite .b (.block digit) (.block word)),
  .block (carry ++ [.alu .add .ecx (.imm 4), .mov .eax (.mem (kp pN4)), .alu .add .eax (.reg .eax),
    .alu .cmp .ecx (.reg .eax)])]

/-- The carry cleared, then the columns. -/
def columns : Prog isa := .seq
  (.block [.mov .ebx (.mem (kp pS)), .mov .eax (.imm 0), .store (at_ .ebx offC) .eax,
    .store (at_ .ebx (offC + 4)) .eax, .mov .ecx (.imm 0)])
  (.loop column .ne)

/-! ## The reduction -/

/-- The frame's parameter `i` outside the MCDT frame. -/
def op (i : Nat) : MemOp := prm 0 i

/-- The result's top word, the last carry's low word, after its `N` words. -/
def top : List Instr :=
  [.mov .ebx (.mem (op pS)), .mov .esi (.mem (op pN4)), .alu .add .esi (.reg .esi),
    .alu .add .esi (.reg .ebx), .mov .eax (.mem (at_ .ebx offC)), .store (at_ .esi offW) .eax]

/-- `ebp` at `T`, the result's `N` words, and `ebx` at the quotient digits,
no longer needed. -/
def ptrs : List Instr :=
  [.mov .ebx (.mem (op pS)), .alu .add .ebx (.imm (BitVec.ofNat 32 offW)), .mov .ebp (.mem (op pN4)),
    .alu .add .ebp (.reg .ebx)]

/-- `D = T - M` over `N` words into the quotient digits' words, the borrow a
mask in `ecx`, with `edi` counting `4 N` bytes down; `ebp` ends at `T`'s top
word. The loop is the run-time width multiplication's. -/
def subM : Prog isa := .seq
  (.block (ptrs ++ [.mov .esi (.mem (op pM)), .mov .edi (.mem (op pN4)), .mov .ecx (.imm 0)]))
  (.loop (.block ([.mov .eax (.mem (at_ .ebp 0))] ++ Rt.restore ++
    [.alu .sbb .eax (.mem (at_ .esi 0)), .store (at_ .ebx 0) .eax, .alu .sbb .ecx (.reg .ecx),
      .alu .add .ebp (.imm 4), .alu .add .esi (.imm 4), .alu .add .ebx (.imm 4),
      .alu .sub .edi (.imm 4)])) .ne)

/-- `O = D` where the mask (from `T`'s top word and the borrow, `Rt.mask`)
is all ones, else `T`; the loop is the run-time width multiplication's. -/
def select : Prog isa := .seq
  (.block (ptrs ++ [.mov .esi (.mem (op pO)), .mov .edi (.mem (op pN4))]))
  (.loop (.block [.mov .eax (.mem (at_ .ebp 0)), .mov .edx (.mem (at_ .ebx 0)),
    .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
    .store (at_ .esi 0) .eax, .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .add .esi (.imm 4),
    .alu .sub .edi (.imm 4)]) .ne)

/-- The kernel, in the frame of the parameters: the columns in an MCDT frame, then the reduction. -/
def kernel : Prog isa := seqs [
  .frame (.mcdtEnter .eax) columns .mcdtLeave,
  .block top, subM, .block Rt.mask, select]

/-- The parameters' frame around the kernel; the parameters are in `ebp`
(`A`), `edi` (`B`), `esi` (`M`), `edx` (`O`), `ecx` (scratch), `ebx`
(`-M⁻¹`'s address) and `eax` (`4 N`). -/
def withParams : Prog isa := .frame (.push [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp]) kernel (.pop .eax 7)

/-- The callee-saved registers back from their frame, `ebx` by its pop. -/
def restoreRegs : List Instr :=
  [.mov .ebp (.mem (at_ .esp 0)), .mov .edi (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8))]

/-- A function: the callee-saved registers saved, the parameters from `params`, the kernel. -/
def body (params : List Instr) : Prog isa :=
  .frame (.push [.ebx, .esi, .edi, .ebp]) (seqs [.block params, withParams, .block restoreRegs]) (.pop .ebx 4)

/-! ## The two functions' parameters -/

/-- The argument `i` of `vg_rsa_mont_mul_at`, past the saved registers. -/
def atArg (i : Nat) : MemOp := at_ .esp (20 + 4 * i)

/-- `r = ws + ` the offset in argument `i`. -/
def atPtr (r : Reg) (i : Nat) : List Instr := [.mov r (.mem (atArg 0)), .alu .add r (.mem (atArg i))]

/-- `vg_rsa_mont_mul_at (ws, ws_len, n, m, inv, s, o, a, b)`: the numbers at
the offsets, `4 N = 8 n`. -/
def atParams : List Instr :=
  atPtr .ebp 7 ++ atPtr .edi 8 ++ atPtr .esi 3 ++ atPtr .edx 6 ++ atPtr .ecx 5 ++ atPtr .ebx 4 ++
    [.mov .eax (.mem (atArg 2)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)]

/-- The argument `i` of `vg_rsa_mont_mul`, past the saved registers. -/
def prArg (i : Nat) : MemOp := at_ .esp (20 + 4 * i)

/-- `r` = the address of the array whose index is argument `i`, from the
header (`t` changes): the header's word `8 + j`, whose high half is zero. -/
def prPtr (r : Reg) (i : Nat) (t : Reg) : List Instr :=
  [.mov r (.mem (prArg 0)), .mov t (.mem (prArg i)), .alu .add t (.reg t), .alu .add t (.reg t),
    .alu .add t (.reg t), .alu .add r (.reg t), .mov r (.mem (at_ r 64))]

/-- `vg_rsa_mont_mul (ws, ws_len, o, a, b)`: the arrays `a`, `b` and `o`, the
modulus (array 0), the scratch (array 2), `-m⁻¹` in header word 7 and `4 N =
8 w` from header word 6. -/
def preparedParams : List Instr :=
  prPtr .ebp 3 .eax ++ prPtr .edi 4 .eax ++ prPtr .edx 2 .eax ++
    [.mov .ebx (.mem (prArg 0)), .mov .esi (.mem (at_ .ebx 64)), .mov .ecx (.mem (at_ .ebx 80)),
      .mov .eax (.mem (at_ .ebx 48)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .ebx (.imm 56)]

def atBody : Prog isa := body atParams
def preparedBody : Prog isa := body preparedParams

end VG.Impl.Mont.X86.Sse2
