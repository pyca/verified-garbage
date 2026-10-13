module

public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Impl.Rsa.X86_64.Checked

/-!
# BoringSSL's `RSA_check_key` on x86-64

`vg_rsa_check_key(n, n_len, e, e_len, d, d_len, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the first six
arguments in registers, the others on the stack.

`e` is checked as `vg_rsa_public_checked` checks it, then `n` as
`vg_rsa_public` does: both are public, and the code returns 0 at once if
either is refused. The rest works in one workspace of `vg_rsa_public`'s
layout (`Impl/Bignum/X86_64.lean`) for `w = ⌈n_len / 8⌉` words, every private
value loaded into an array of `w` words, and its timing depends only on the
lengths and on `n` and `e`: each check gives a mask, and'ed into the
header's `sMask`, which is returned as 0 or 1 at the end.

* `d < n`, `dP < p - 1`, `dQ < q - 1` and `qInv < p`: the borrow of a
  subtraction (`ltMask`).
* `p q = n`: the product, compared with `n` (`Crt.eqCheck`).
* `d e ≡ 1 (mod p - 1)` and the others: the product `x` of `d`, `dP` or
  `dQ` and `e` (`w + 2` words), or of `q` and `qInv` (`2 w + 2` words), is
  reduced modulo `m` (`p - 1`, `q - 1` or `p`) by restoring division
  (`reduce`): from the top bit of `x` down, `r := 2 r + b mod m` (`dblIn`,
  `vg_rsa_public`'s doubling with the bit as the carry into the low word),
  and `r` compared with 1 (`eqOne`).

`p < n` and `q < n` need no computation: `p` and `q` are shorter than `n`,
which is at least `256^(n_len - 1)`.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.CheckKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-! ## Header slots and arrays

`sN`, `sK` and `sMask` are `vg_rsa_public`'s; `sEv` holds `e`'s value. -/

def sD : Nat := sFn 0
def sE : Nat := sFn 3
def sElen : Nat := sFn 4
def sDlen : Nat := sFn 5
def sP : Nat := sFn 7
def sPlen : Nat := sFn 8
def sQ : Nat := sFn 9
def sQlen : Nat := sFn 10
def sDP : Nat := sFn 11
def sDQ : Nat := sFn 12
def sQI : Nat := sFn 13
def sEv : Nat := sFn 14

/-- The arrays: `n` (`aN`), the operand `x` (`aX`, also `dblIn`'s
accumulator), the product (`aAcc` and `aTmp`, `2 w + 4` words), the modulus
`m` (4), `dblIn`'s temporary (5), the remainder `r` and the second factor
of a product (6), and the number 1 (`aOne`). -/
def aM : Nat := 4
def aT : Nat := 5
def aR : Nat := 6

/-- The stack argument `i` (from 1). -/
def stk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-- Header slot `i` of the working space at `r11`. -/
def ws (i : Nat) : MemOp := { base := .r11, disp := 8 * i }

/-! ## Entry and exit -/

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`; then `e` and `e_len` into `r8` and `r9`
for `expCheck`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem (stk 11))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store (ws i) r) ++
  ([.store (ws sN) .rdi, .store (ws sK) .rsi, .store (ws sE) .rdx, .store (ws sElen) .rcx,
    .store (ws sD) .r8, .store (ws sDlen) .r9,
    .mov .rax (.mem (stk 1)), .store (ws sP) .rax, .mov .rax (.mem (stk 2)), .store (ws sPlen) .rax,
    .mov .rax (.mem (stk 3)), .store (ws sQ) .rax, .mov .rax (.mem (stk 4)), .store (ws sQlen) .rax,
    .mov .rax (.mem (stk 5)), .store (ws sDP) .rax, .mov .rax (.mem (stk 7)), .store (ws sDQ) .rax,
    .mov .rax (.mem (stk 9)), .store (ws sQI) .rax,
    .mov .rdi (.reg .r11), .mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx)] : List Instr)

/-- 0 returned. -/
def fail : List Instr := ([.mov32 .rax (.imm 0)] : List Instr) ++ exit

/-! ## The pieces -/

/-- `[j] := ` the number of the bytes whose pointer and length are in header
slots `slotPtr` and `slotLen`. -/
def loadNum (j slotPtr slotLen : Nat) : List (Prog isa) := [
  Crt.zeroArr j,
  .block [.mov .rsi (.mem (hdr slotPtr)), .mov .rcx (.mem (hdr slotLen)), .mov .rbx (.mem (hdr (sArr j)))],
  loadBE]

/-- `sMask &= ` the mask of `[a] < [b]` over `w` words: the borrow of
`[a] - [b]`. -/
def ltMask (a b : Nat) : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr a))), .mov .r10 (.mem (hdr (sArr b))),
    .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
  .block [.alu .and .rbp (.mem (hdr sMask)), .store (hdr sMask) .rbp]]

/-- `[aM] := [aM] - 1` over `w` words: a borrow chain with a borrow in. -/
def decM : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aM))), .mov32 .rbp (.imm 0),
    .alu .sub .rbp (.imm 1)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.imm 0), .store (ix .rbx .r14) .rax,
    cfToRbp]]

/-- `acc := [aX] e` (`w + 2` words). -/
def mulE : List (Prog isa) := [
  .block [.mov .r8 (.mem (hdr (sArr aAcc))), .mov .r12 (.mem (hdr sW))],
  zeroAccLoop,
  .block [.mov .rcx (.mem (hdr sEv)), .mov .r9 (.mem (hdr (sArr aX))), .mov .r8 (.mem (hdr (sArr aAcc)))],
  mulAddRow]

/-- `acc := [aX] [aR]` (`2 w + 2` words). -/
def mulXR : List (Prog isa) :=
  Crt.zeroAccs ++ [
  .block [.mov .r11 (.mem (hdr (sArr aX))), .mov .r10 (.mem (hdr sW)), .mov .r9 (.mem (hdr (sArr aR))),
    .mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aAcc)))],
  Crt.mulRows]

/-- `[rbx] := 2 [rbx] + c mod [r10]` over `w` words (`r12`), for the carry
`c` in `rbp` (0 or all ones): `vg_rsa_public`'s `double` from the carry
`c`, with the accumulator at `r8` and the temporary at `rsi`. -/
def dblIn : Prog isa :=
  .seq (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.reg .rax),
      .store (ix .r8 .r14) .rax, cfToRbp])
    (.seq (.block [.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax])
      (.seq subMod selectAcc))

/-- One bit of `x`: the top bit of `r15` shifted out into the mask `rbp`,
`r := 2 r + b mod m`, and `r11` counted down. -/
def bitStep : Prog isa :=
  .seq (.block [.mov .rax (.reg .r15), .alu .add .rax (.reg .rax), .mov .r15 (.reg .rax),
      .alu .sbb .rbp (.reg .rbp)])
    (.seq dblIn (.block [.alu .sub .r11 (.imm 1)]))

/-- One word of `x`, from the top: word `r13 - 1` into `r15`, then its 64
bits. -/
def wordStep : Prog isa :=
  .seq (.block [.alu .sub .r13 (.imm 1), .mov .r15 (.mem (ix .r9 .r13)), .mov32 .r11 (.imm 64)])
    (.seq (.loop bitStep .ne) (.block [.alu .test .r13 (.reg .r13)]))

/-- `[aR] := acc mod [aM]` for the accumulator's `r13 = cnt` words (`cnt`
the instructions that compute it from `w` in `r13`), by restoring division:
`r := 0`, then `wordStep` for each word, from the top. -/
def reduce (cnt : List Instr) : List (Prog isa) := [
  Crt.zeroArr aR,
  .block (([.mov .rbx (.mem (hdr (sArr aR))), .mov .r10 (.mem (hdr (sArr aM))), .mov .r8 (.mem (hdr (sArr aX))),
    .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aT))), .mov .r9 (.mem (hdr (sArr aAcc))),
    .mov .r13 (.reg .r12)] : List Instr) ++ cnt),
  .loop wordStep .ne]

/-- `w + 2` and `2 w + 2` words, from `w` in `r13`. -/
def cntE : List Instr := [.alu .add .r13 (.imm 2)]
def cntXR : List Instr := [.alu .add .r13 (.reg .r13), .alu .add .r13 (.imm 2)]

/-- `sMask &= ` the mask of `[aR] = 1` over `w` words: the OR of the words of
`[aR] XOR [aOne]` is zero. -/
def eqOne : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aR))), .mov .r10 (.mem (hdr (sArr aOne))),
    .mov32 .rbp (.imm 0)],
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)],
  .block [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .alu .and .rbp (.mem (hdr sMask)),
    .store (hdr sMask) .rbp]]

/-- The checks modulo `X - 1` for the prime `X` (pointer and length in
slots `sX` and `sXlen`) and its exponent `dX` (pointer in `sDX`):
`dX < X - 1`, `d e ≡ 1` and `e dX ≡ 1`. -/
def modChecks (sX sXlen sDX : Nat) : List (Prog isa) :=
  loadNum aM sX sXlen ++ decM ++
  loadNum aX sDX sXlen ++ ltMask aX aM ++
  loadNum aX sD sDlen ++ mulE ++ reduce cntE ++ eqOne ++
  loadNum aX sDX sXlen ++ mulE ++ reduce cntE ++ eqOne

/-- The computation, once `n` and `e` are known valid. -/
def main : Prog isa := seqs (
  [.block head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx,
    .block [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]] ++
  -- `d < n`
  loadNum aX sD sDlen ++ ltMask aX aN ++
  -- `p q = n`
  loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ Crt.eqCheck ++
  -- modulo `p - 1` and `q - 1`
  modChecks sP sPlen sDP ++ modChecks sQ sQlen sDQ ++
  -- `qInv < p` and `q qInv ≡ 1 (mod p)`
  loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
  loadNum aR sQ sQlen ++ mulXR ++ reduce cntXR ++ eqOne ++
  [.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)])

/-- `vg_rsa_check_key`. -/
def code : Prog isa := seqs [
  .block entry,
  Checked.expCheck,
  .ite .ne (.block fail)
    (seqs [.block (([.store (hdr sEv) .r11, .mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid),
      .ite .ne (.block fail) main])]

end VG.Impl.Rsa.X86_64.CheckKey
