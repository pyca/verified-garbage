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

/-- The products `X_j Y_j` of four words, `esi` at `X_j` and `edi` at `Y_j`,
reading a fifth: `movdqu` reads words `j` to `j + 3` (`pmuludq` multiplies
words `j` and `j + 2`) and, 4 bytes on, `j + 1` to `j + 4`. -/
def quadMul : List Instr :=
  [.movdquLoad .xmm2 (at_ .esi 0), .movdquLoad .xmm3 (at_ .edi 0), .pmuludq .xmm2 .xmm3,
    .movdquLoad .xmm4 (at_ .esi 4), .movdquLoad .xmm5 (at_ .edi 4), .pmuludq .xmm4 .xmm5] ++
    acc .xmm2 ++ acc .xmm4

/-- Four products while a fifth word follows: the pointers up 16 bytes and
the count of bytes left, `ebp`, down 16; CF clear if at least five words
remain. -/
def quadBody : List Instr :=
  quadMul ++ [.alu .add .esi (.imm 16), .alu .add .edi (.imm 16), .alu .sub .ebp (.imm 16), .alu .cmp .ebp (.imm 20)]

/-- The products of four words, reading only them: `pshufd` moves words
`j + 1` and `j + 3` to doublewords 0 and 2. -/
def quadLastMul : List Instr :=
  [.movdquLoad .xmm2 (at_ .esi 0), .movdquLoad .xmm3 (at_ .edi 0), .xop (.pshufd .xmm4 .xmm2 0x31),
    .xop (.pshufd .xmm5 .xmm3 0x31), .pmuludq .xmm2 .xmm3, .pmuludq .xmm4 .xmm5] ++ acc .xmm2 ++ acc .xmm4

/-- The last four products. -/
def quadLast : List Instr :=
  quadLastMul ++ [.alu .add .esi (.imm 16), .alu .add .edi (.imm 16), .alu .sub .ebp (.imm 16)]

/-- The products of two words: `movq` reads them, `punpckldq` puts them in
doublewords 0 and 2. -/
def pairMul : List Instr :=
  [.movqLoad .xmm2 (at_ .esi 0), .movqLoad .xmm3 (at_ .edi 0), .xop (.bin .punpckldq .xmm2 .xmm2),
    .xop (.bin .punpckldq .xmm3 .xmm3), .pmuludq .xmm2 .xmm3] ++ acc .xmm2

/-- Two products. -/
def pair : List Instr :=
  pairMul ++ [.alu .add .esi (.imm 8), .alu .add .edi (.imm 8), .alu .sub .ebp (.imm 8)]

/-- One product. -/
def single : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .xop (.movd .xmm2 .eax), .mov .eax (.mem (at_ .edi 0)), .xop (.movd .xmm3 .eax),
    .pmuludq .xmm2 .xmm3] ++ acc .xmm2

/-- `Σ X_j Y_j` for `j` below `ebp / 4`, into the sums, for `esi` at `X` and
`edi` at `Y`: four products at a time while a fifth word follows, then four,
two and one. Only the count, not a pointer, controls the loops. Uses `eax`,
`esi`, `edi` and `ebp`. -/
def dot : Prog isa := seqs [
  .block [.alu .cmp .ebp (.imm 20)],
  .ite .ae (.loop (.block quadBody) .ae) (.block []),
  .block [.alu .cmp .ebp (.imm 16)],
  Code.iteCold .ae (.block quadLast) (.block []),
  .block [.alu .cmp .ebp (.imm 8)],
  .ite .ae (.block pair) (.block []),
  .block [.alu .cmp .ebp (.imm 4)],
  .ite .ae (.block single) (.block [])]

/-- A parameter's value into `r`. -/
def ld (i : Nat) (r : Reg) : List Instr := [.mov r (.mem (kp i))]

/-- `r = S + 24 + d + j (4 N)`: the quotient digits (`j = 0`) or the copy of
`A` (`j = 1`), plus `d`; `eax = 4 N`. -/
def ldW (r : Reg) (d j : Nat) : List Instr :=
  [.mov r (.mem (kp pS)), .alu .add r (.imm (BitVec.ofNat 32 (offW + d))), .mov .eax (.mem (kp pN4))] ++
    List.replicate j (.alu .add r (.reg .eax))

/-! ## A column

The quotient digits are stored in reverse, `Q_j` at word `N - 1 - j` of
`S + 24`, and `A` is copied in reverse after them (`A'`, `A_i` at word
`N - 1 - i` of `S + 24 + 4 N`), so the products of a column are those of
words of two numbers at the same index from two pointers, which `dot` reads
without shuffles. While `k < N`, column `k` (`ecx = 4 k`) has the products
`A'_t B_(t+k+1-N)` and `Q'_t M_(t+k+1-N)` for `N - 1 - k ≤ t < N`; from
`k = N` on, for `t ≤ 2 N - 2 - k`, and its word of the result replaces `Q_(k-N)`,
dead. The two latest digits, `Q_(k-1)` and `Q_(k-2)`, are kept in `xmm6`
(quadwords 0 and 1) and multiplied by `M_1` and `M_2` (doublewords 0 and 2 of
`xmm7`) rather than read by `movdqu`, whose 16 bytes would wait for their
stores to complete. -/

/-- `ebx = 4 ⌊(k + 1) / 2⌋`, the products with `i < k - i`. -/
def endHalf : List Instr :=
  [.mov .ebx (.reg .ecx), .alu .add .ebx (.imm 4), .shift .shr .ebx 3, .alu .add .ebx (.reg .ebx),
    .alu .add .ebx (.reg .ebx)]

/-- For even `k`, `A_(k/2)²`: `ebx = 4 ⌊(k + 1) / 2⌋` from `endHalf` is
`2 k` exactly when `k` is even, and then the diagonal's offset. -/
def diag : Prog isa := .seq
  (.block [.mov .eax (.reg .ebx), .alu .add .eax (.reg .eax), .alu .cmp .eax (.reg .ecx)])
  (.ite .e (.block ([.mov .esi (.mem (kp pA)), .alu .add .esi (.reg .ebx),
      .mov .eax (.mem (at_ .esi 0)), .xop (.movd .xmm2 .eax), .pmuludq .xmm2 .xmm2] ++ acc .xmm2))
    (.block []))

/-- `ebp = 4 (2 N - 1 - k)`, the products from `k = N` on; `eax = 4 N`. -/
def lenHigh : List Instr :=
  [.mov .eax (.mem (kp pN4)), .mov .ebp (.reg .eax), .alu .add .ebp (.reg .eax), .alu .sub .ebp (.imm 4),
    .alu .sub .ebp (.reg .ecx)]

/-- The products of `A` and `B` (`sq = false`) or a square's (`sq`: those
with `i < k - i`, doubled, and the diagonal), while `k < N` (`hi = false`)
or from `k = N` on (`hi`). -/
def input (sq hi : Bool) : Prog isa :=
  match sq, hi with
  | false, false => .seq
    (.block ([.mov .ebp (.reg .ecx), .alu .add .ebp (.imm 4)] ++ ldW .esi 0 2 ++
      [.alu .sub .esi (.reg .ebp)] ++ ld pB .edi))
    dot
  | false, true => .seq
    (.block (lenHigh ++ ldW .esi 0 1 ++ ld pB .edi ++
      [.alu .add .edi (.reg .ecx), .alu .add .edi (.imm 4), .alu .sub .edi (.reg .eax)]))
    dot
  | true, hi => seqs [
    .block (endHalf ++ (if hi then
        [.mov .eax (.mem (kp pN4)), .mov .ebp (.reg .ebx), .alu .add .ebp (.reg .eax), .alu .sub .ebp (.reg .ecx),
          .alu .sub .ebp (.imm 4)]
      else [.mov .ebp (.reg .ebx)]) ++
      ldW .esi 0 2 ++ [.alu .sub .esi (.reg .ebx)] ++ ld pA .edi ++
      [.alu .add .edi (.reg .ecx), .alu .add .edi (.imm 4), .alu .sub .edi (.reg .ebx)]),
    dot,
    .block [.xop (.bin .paddq .xmm0 .xmm0), .xop (.bin .paddq .xmm1 .xmm1)],
    diag]

/-- The products of the quotient digits and `M`: while `k < N`, those of
`Q_j`, `j ≤ k - 3`, then the two in `xmm6`. -/
def reduce (hi : Bool) : Prog isa :=
  if hi then .seq
    (.block (lenHigh ++ ldW .esi 0 0 ++ ld pM .edi ++
      [.alu .add .edi (.reg .ecx), .alu .add .edi (.imm 4), .alu .sub .edi (.reg .eax)]))
    dot
  else seqs [
    .block [.mov .ebp (.reg .ecx), .alu .sub .ebp (.imm 8)],
    Code.iteCold .b (.block [.mov .ebp (.imm 0)]) (.block []),
    .block (ldW .esi 8 1 ++ [.alu .sub .esi (.reg .ecx)] ++ ld pM .edi ++ [.alu .add .edi (.imm 12)]),
    dot,
    .block ([.xop (.bin .movdqa .xmm2 .xmm6), .pmuludq .xmm2 .xmm7] ++ acc .xmm2)]

/-- The lanes added into lane 0, the sums stored, and `Z = S + c`: `eax`
its low word, `edx` its high word; `ebx` the scratch pointer. -/
def fold : List Instr :=
  [.xop (.bin .movdqa .xmm2 .xmm0), .xop (.shift .psrldq .xmm2 8), .xop (.bin .paddq .xmm0 .xmm2),
    .xop (.bin .movdqa .xmm2 .xmm1), .xop (.shift .psrldq .xmm2 8), .xop (.bin .paddq .xmm1 .xmm2),
    .mov .ebx (.mem (kp pS)), .movqStore (at_ .ebx offS) .xmm0, .movqStore (at_ .ebx offH) .xmm1,
    .mov .eax (.mem (at_ .ebx offS)), .alu .add .eax (.mem (at_ .ebx offC)),
    .mov .edx (.mem (at_ .ebx (offS + 4))), .alu .adc .edx (.mem (at_ .ebx (offC + 4)))]

/-- `k < N`: the digit `q = Z_lo (-M⁻¹) mod 2³²` stored at word `N - 1 - k`
and into `xmm6`, and `q M_0` added to `Z` (whose low word becomes zero; `edx`
its high word) and its high word to `H`. -/
def digit : List Instr :=
  [.mov .esi (.reg .edx), .mov .edi (.reg .eax),
    .mov .edx (.mem (kp pInv)), .mov .edx (.mem (at_ .edx 0)), .mul .edx,
    .mov .edx (.mem (kp pN4)), .alu .add .edx (.reg .ebx), .alu .sub .edx (.reg .ecx),
    .store (at_ .edx (offW - 4)) .eax,
    .xop (.movd .xmm2 .eax), .xop (.bin .punpcklqdq .xmm2 .xmm6), .xop (.bin .movdqa .xmm6 .xmm2),
    .mov .edx (.mem (kp pM)), .mov .edx (.mem (at_ .edx 0)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .adc .esi (.reg .edx),
    .mov .eax (.mem (at_ .ebx offH)), .alu .add .eax (.reg .edx), .store (at_ .ebx offH) .eax,
    .mov .eax (.mem (at_ .ebx (offH + 4))), .alu .adc .eax (.imm 0), .store (at_ .ebx (offH + 4)) .eax,
    .mov .edx (.reg .esi)]

/-- `k ≥ N`: the result's word `Z_lo` stored at word `2 N - 1 - k`, over `Q_(k-N)`. -/
def word : List Instr :=
  [.mov .esi (.mem (kp pN4)), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .ebx), .alu .sub .esi (.reg .ecx),
    .store (at_ .esi (offW - 4)) .eax]

/-- The carry `H + (L + c)_hi`: its low word `Z_hi` (`edx`), its high word
`H_hi + [Z_hi < H_lo]`. -/
def carry : List Instr :=
  [.store (at_ .ebx offC) .edx, .alu .cmp .edx (.mem (at_ .ebx offH)),
    .mov .eax (.mem (at_ .ebx (offH + 4))), .alu .adc .eax (.imm 0), .store (at_ .ebx (offC + 4)) .eax]

/-- Column `k` (`ecx = 4 k`), then `ecx` up a word; ZF after the last of the
phase, `k = N - 1` or `k = 2 N - 1`. -/
def column (sq hi : Bool) : Prog isa := seqs [
  .block [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)],
  input sq hi, reduce hi, .block fold,
  .block ((if hi then word else digit) ++ carry ++ [.alu .add .ecx (.imm 4), .mov .eax (.mem (kp pN4))] ++
    (if hi then [.alu .add .eax (.reg .eax)] else []) ++ [.alu .cmp .ecx (.reg .eax)])]

/-- `A'`: `A_i` at word `N - 1 - i` of `S + 24 + 4 N`, `ebx` from its end
down, `esi` up `A`, `edi` counting `4 N` bytes. -/
def copyA : Prog isa := .seq
  (.block (ldW .ebx 0 2 ++ ld pA .esi ++ ld pN4 .edi))
  (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .alu .sub .ebx (.imm 4), .store (at_ .ebx 0) .eax,
    .alu .add .esi (.imm 4), .alu .sub .edi (.imm 4)]) .ne)

/-- `xmm6 = 0` and `M_1`, `M_2` in doublewords 0 and 2 of `xmm7` (`M_2` if
`N > 2`). -/
def window : Prog isa := .seq
  (.block [.xop (.bin .pxor .xmm6 .xmm6), .mov .eax (.mem (kp pM)), .mov .ebx (.mem (at_ .eax 4)),
    .xop (.movd .xmm7 .ebx), .mov .ebx (.mem (kp pN4)), .alu .cmp .ebx (.imm 12)])
  (Code.iteCold .ae (.block [.mov .ebx (.mem (at_ .eax 8)), .xop (.movd .xmm2 .ebx), .xop (.bin .punpcklqdq .xmm7 .xmm2)])
    (.block []))

/-- The columns of one kind: those with `k < N`, then the others. -/
def phases (sq : Bool) : Prog isa := .seq (.loop (column sq false) .ne) (.loop (column sq true) .ne)

/-- `A'`, the carry cleared, the window, then the columns. -/
def columns : Prog isa := seqs [
  copyA,
  .block [.mov .ebx (.mem (kp pS)), .mov .eax (.imm 0), .store (at_ .ebx offC) .eax,
    .store (at_ .ebx (offC + 4)) .eax, .mov .ecx (.imm 0)],
  window,
  .block [.mov .eax (.mem (kp pA)), .mov .ebx (.mem (kp pB)), .alu .cmp .eax (.reg .ebx)],
  .ite .e (phases true) (phases false)]

/-! ## The reduction -/

/-- The frame's parameter `i` outside the MCDT frame. -/
def op (i : Nat) : MemOp := prm 0 i

/-- `ebp` at the end of `T`, the result's `N` words in reverse at `S + 24`,
and `ebx` at `A'`, no longer needed. -/
def ptrs : List Instr :=
  [.mov .ebp (.mem (op pS)), .alu .add .ebp (.imm (BitVec.ofNat 32 offW)), .mov .eax (.mem (op pN4)),
    .alu .add .ebp (.reg .eax), .mov .ebx (.reg .ebp)]

/-- `D = T - M` over `N` words into `A'`, the borrow a mask in `ecx`, with
`edi` counting `4 N` bytes down and `ebp` down `T`'s words. -/
def subM : Prog isa := .seq
  (.block (ptrs ++ [.mov .esi (.mem (op pM)), .mov .edi (.mem (op pN4)), .mov .ecx (.imm 0)]))
  (.loop (.block ([.alu .sub .ebp (.imm 4), .mov .eax (.mem (at_ .ebp 0))] ++ Rt.restore ++
    [.alu .sbb .eax (.mem (at_ .esi 0)), .store (at_ .ebx 0) .eax, .alu .sbb .ecx (.reg .ecx),
      .alu .add .esi (.imm 4), .alu .add .ebx (.imm 4), .alu .sub .edi (.imm 4)])) .ne)

/-- The mask from `T`'s top word, the last carry's low word, and the borrow:
all ones if `T ≥ M`. -/
def mask : List Instr :=
  [.mov .eax (.mem (op pS)), .mov .eax (.mem (at_ .eax offC))] ++ Rt.restore ++
    [.alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm (-1)), .mov .ecx (.reg .eax)]

/-- `O = D` where the mask is all ones, else `T`. -/
def select : Prog isa := .seq
  (.block (ptrs ++ [.mov .esi (.mem (op pO)), .mov .edi (.mem (op pN4))]))
  (.loop (.block [.alu .sub .ebp (.imm 4), .mov .eax (.mem (at_ .ebp 0)), .mov .edx (.mem (at_ .ebx 0)),
    .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
    .store (at_ .esi 0) .eax, .alu .add .ebx (.imm 4), .alu .add .esi (.imm 4),
    .alu .sub .edi (.imm 4)]) .ne)

/-- The kernel, in the frame of the parameters: the columns in an MCDT frame, then the reduction. -/
def kernel : Prog isa := seqs [
  .frame (.mcdtEnter .eax) columns .mcdtLeave,
  subM, .block mask, select]

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
