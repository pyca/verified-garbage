import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey

/-!
# The checks of `RSA_check_key` on the CRT form on x86-64

`vg_rsa_check_crt_key(n, n_len, e, e_len, p, p_len, q, q_len, dp, dp_len,
dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the first six arguments
in registers, the others on the stack.

`vg_rsa_check_key`'s code (`CheckKey.lean`) without the checks of `d`, and
with shorter remainders. Its entry stores the arguments in the same header
slots, `p` and `p_len` also in `d`'s (which nothing reads), so that the
checks run in `vg_rsa_check_key`'s context. `e` is checked as
`vg_rsa_public_checked` checks it, then `n` as `vg_rsa_public` does: both are
public, and the code returns 0 at once if either is refused. The rest works
in one workspace of `vg_rsa_public`'s layout for `w = ⌈n_len / 8⌉` words,
and its timing depends only on the lengths and on `n` and `e`: each check
gives a mask, and'ed into the header's `sMask`, which is returned as 0 or 1
at the end.

* `p q = n`: the product, compared with `n` (`Crt.eqCheck`).
* `dP < p - 1`, `dQ < q - 1` and `qInv < p`: the borrow of a subtraction
  (`ltMask`).
* `e dX ≡ 1 (mod X - 1)` and `q qInv ≡ 1 (mod p)`: the product `x` of `dX`
  and `e` (`w + 2` words), or of `q` and `qInv` (`2 w + 2` words), reduced
  modulo `m` (`X - 1` or `p`) by restoring division (`reduceTop`) over
  numbers of `w' = ⌈X_len / 8⌉` words, the length of `m`. When the
  comparison before it holds, the quotient is small: `x < 2^(64 c) m` for
  `c = 1` (`e < 2^33`, `dX < m`) and for `c = ⌈q_len / 8⌉` (`qInv < p`), so
  `r` starts as `x`'s words from `c` up, which are `⌊x / 2^(64 c)⌋ < m`, and
  only `x`'s low `c` words are divided, a bit at a time. When it does not
  hold, the remainder is not used: the mask is clear.
-/

namespace VG.Impl.Rsa.X86_64.CheckCrtKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.CheckKey (sD sDlen sP sPlen sQ sQlen sDP sDQ sQI sEv aM aT aR stk ws fail
  loadNum ltMask decM mulE mulXR wordStep eqOne)

/-! ## Entry -/

/-- Save the callee-saved registers and the arguments in the header at
`scratch` (stack argument 8), in `vg_rsa_check_key`'s slots, with `p` and
`p_len` in `d`'s too, and its base in `rdi`; then `e` and `e_len` into `r8`
and `r9` for `expCheck`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem (stk 9))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store (ws i) r) ++
  ([.store (ws sN) .rdi, .store (ws sK) .rsi, .store (ws CheckKey.sE) .rdx, .store (ws CheckKey.sElen) .rcx,
    .store (ws sD) .r8, .store (ws sDlen) .r9, .store (ws sP) .r8, .store (ws sPlen) .r9,
    .mov .rax (.mem (stk 1)), .store (ws sQ) .rax, .mov .rax (.mem (stk 2)), .store (ws sQlen) .rax,
    .mov .rax (.mem (stk 3)), .store (ws sDP) .rax, .mov .rax (.mem (stk 5)), .store (ws sDQ) .rax,
    .mov .rax (.mem (stk 7)), .store (ws sQI) .rax,
    .mov .rdi (.reg .r11), .mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx)] : List Instr)

/-! ## Remainders with a small quotient -/

/-- `r12 := ⌈len / 8⌉`, the words of the length in header slot `sl`. -/
def lenWords (sl : Nat) : List Instr :=
  [.mov .r12 (.mem (hdr sl)), .alu .add .r12 (.imm 7), .shift .shr .r12 3]

/-- `c = 1`, into `r13`. -/
def topE : List Instr := [.mov32 .r13 (.imm 1)]

/-- `c = ⌈q_len / 8⌉`, into `r13`. -/
def topQ : List Instr := [.mov .r13 (.mem (hdr sQlen)), .alu .add .r13 (.imm 7), .shift .shr .r13 3]

/-- `[aR] := x mod [aM]` for the number `x` of the accumulator, given that
`⌊x / 2^(64 c)⌋ < [aM]` for the `c` that `top` puts in `r13`, over numbers
of `⌈len / 8⌉` words (the length in slot `sl`): `r := 0`, `x`'s words from
`c` up into `r`'s low `⌈len / 8⌉`, then `wordStep` for each of `x`'s low `c`
words, from the top. -/
def reduceTop (sl : Nat) (top : List Instr) : List (Prog isa) := [
  Crt.zeroArr aR,
  .block (lenWords sl ++ top ++ ([.mov .rax (.reg .r13), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .mov .rsi (.mem (hdr (sArr aAcc))), .alu .add .rsi (.reg .rax),
    .mov .rbx (.mem (hdr (sArr aR)))] : List Instr)),
  copyWords,
  .block [.mov .rbx (.mem (hdr (sArr aR))), .mov .r10 (.mem (hdr (sArr aM))), .mov .r8 (.mem (hdr (sArr aX))),
    .mov .rsi (.mem (hdr (sArr aT))), .mov .r9 (.mem (hdr (sArr aAcc)))],
  .loop wordStep .ne]

/-- The checks modulo `X - 1` for the prime `X` (pointer and length in
slots `sX` and `sXlen`) and its exponent `dX` (pointer in `sDX`):
`dX < X - 1` and `e dX ≡ 1`. -/
def modChecks (sX sXlen sDX : Nat) : List (Prog isa) :=
  loadNum aM sX sXlen ++ decM ++
  loadNum aX sDX sXlen ++ ltMask aX aM ++ mulE ++ reduceTop sXlen topE ++ eqOne

/-- The computation, once `n` and `e` are known valid. -/
def main : Prog isa := seqs (
  [.block head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx,
    .block [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]] ++
  -- `p q = n`
  loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ Crt.eqCheck ++
  -- modulo `p - 1` and `q - 1`
  modChecks sP sPlen sDP ++ modChecks sQ sQlen sDQ ++
  -- `qInv < p` and `q qInv ≡ 1 (mod p)`
  loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
  loadNum aR sQ sQlen ++ mulXR ++ reduceTop sPlen topQ ++ eqOne ++
  [.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)])

/-- `vg_rsa_check_crt_key`. -/
def code : Prog isa := seqs [
  .block entry,
  Checked.expCheck,
  .ite .ne (.block fail)
    (seqs [.block (([.store (hdr sEv) .r11, .mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid),
      .ite .ne (.block fail) main])]

end VG.Impl.Rsa.X86_64.CheckCrtKey
