module

public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey

/-!
# The precomputed values of an RSA private key on x86-64

`vg_rsa_private_precompute(pre, pre_len, n, n_len, p, p_len, q, q_len,
scratch, scratch_len)`: the first six arguments in registers, the others on
the stack.

`vg_rsa_check_key`'s code (`CheckKey.lean`): its entry stores the arguments
in that function's header slots, `pre` and `pre_len` in `e`'s, `n` also as
`d`, `p` also as `dP` and `qInv`, and `q` as `dQ` (which nothing reads), so
that the code runs in `vg_rsa_check_key`'s context and loads `n` as it loads
`d`. `n` is checked as
`vg_rsa_public` checks it: it is public, and the code writes zeros to `pre`
and returns 0 at once if it is refused. The rest works in one workspace of
`vg_rsa_public`'s layout for `w = ⌈n_len / 8⌉` words, and its timing depends
only on the lengths and on `n`:

* `p q = n`: the product, compared with `n` (`Crt.eqCheck`), gives the mask
  in `sMask`.
* `n`, `R² mod n`, `R_p mod p` and `R_q mod q` (with `R_X = 2^(64 w_X)` and
  `w_X = max(2, ⌈X_len / 8⌉) ≤ w`), in `pre`'s layout, to the words past
  the eight arrays (`dBase`): the powers of 2 reduced as `vg_rsa_check_key`
  reduces (`reduce`), `2^(128 w)` over the `2 w + 2` words of the
  accumulator and `R_X` over its first `w + 2`.
* Those words, and'ed with the mask, to `pre`, and the mask returned as 0
  or 1.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.CheckKey (sD sDlen sP sPlen sQ sQlen sDP sDQ sQI aM aR stk ws fail loadNum
  mulXR reduce cntE cntXR)

/-! ## Entry -/

/-- Save the callee-saved registers and the arguments in the header at
`scratch` (stack argument 3), in `vg_rsa_check_key`'s slots, `pre` and
`pre_len` in `e`'s and `n` and `n_len` in `d`'s too, with its base in `rdi`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem (stk 3))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store (ws i) r) ++
  ([.store (ws sN) .rdx, .store (ws sK) .rcx, .store (ws CheckKey.sE) .rdi, .store (ws CheckKey.sElen) .rsi,
    .store (ws sD) .rdx, .store (ws sDlen) .rcx, .store (ws sP) .r8, .store (ws sPlen) .r9,
    .store (ws sDP) .r8, .store (ws sQI) .r8,
    .mov .rax (.mem (stk 1)), .store (ws sQ) .rax, .mov .rax (.mem (stk 1)), .store (ws sDQ) .rax,
    .mov .rax (.mem (stk 2)), .store (ws sQlen) .rax,
    .mov .rdi (.reg .r11)] : List Instr)

/-- Zeros to the `pre_len` words of `pre`, and 0 returned. -/
def failZ : Prog isa :=
  .seq (.block [.mov .rbx (.mem (hdr CheckKey.sE)), .mov .r12 (.mem (hdr CheckKey.sElen)), .mov32 .rax (.imm 0)])
    (.seq (wordLoop 0 [.store (ix .rbx .r14) .rax]) (.block fail))

/-! ## The values -/

/-- `rbx :=` the words past the arrays (`8 (w + 2)` bytes past the base of
`aOne`), and `r12 := w`. -/
def dBase : List Instr :=
  [.mov .rbx (.mem (hdr (sArr aOne))), .mov .r12 (.mem (hdr sW)), .mov .rax (.reg .r12),
    .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rbx (.reg .rax)]

/-- `rbx += 8 r12`. -/
def skipW : List Instr := eightW ++ [.alu .add .rbx (.reg .rax)]

/-- `r12 := max(2, ⌈len / 8⌉)` for the length in header slot `sl` (at
least 1). -/
def primeW (sl : Nat) : List Instr :=
  [.mov .r12 (.mem (hdr sl)), .alu .add .r12 (.imm 7), .shift .shr .r12 3, .alu .cmp .r12 (.imm 2),
    .alu .adc .r12 (.imm 0)]

/-- The words of array `j` to the words past the arrays, at the offset and
with the count `r12` that `off` sets from `dBase`'s. -/
def copyOut (off : List Instr) (j : Nat) : List (Prog isa) :=
  [.block (dBase ++ off ++ ([.mov .rsi (.mem (hdr (sArr j)))] : List Instr)), copyWords]

/-- The accumulator's `2 w + 2` words `:= 2^(128 w)`: `aAcc` zero, and word
`w - 2` of `aTmp` 1. -/
def accTop : List (Prog isa) := [
  Crt.zeroArr aAcc,
  .block [.mov .rcx (.mem (hdr sW)), .alu .sub .rcx (.imm 2), .mov32 .rdx (.imm 1), .mov .r12 (.mem (hdr sW))],
  setWord aTmp .rcx]

/-- The accumulator's `w + 2` words `:= 2^(64 w_X)`, for the prime's length
in header slot `sl`. -/
def accPrime (sl : Nat) : List (Prog isa) := [
  .block (primeW sl ++ ([.mov .rcx (.reg .r12), .mov32 .rdx (.imm 1), .mov .r12 (.mem (hdr sW))] : List Instr)),
  setWord aAcc .rcx]

/-- `pre_len` words from `rsi` to `rbx`, each and'ed with the mask in
`rbp`. -/
def maskWords : Prog isa :=
  wordLoop 0 [.mov .rax (.mem (ix .rsi .r14)), .alu .and .rax (.reg .rbp), .store (ix .rbx .r14) .rax]

/-- The words past the arrays, and'ed with `sMask`, to `pre`. -/
def maskOut : List (Prog isa) := [
  .block (dBase ++ ([.mov .rsi (.reg .rbx), .mov .rbx (.mem (hdr CheckKey.sE)), .mov .r12 (.mem (hdr CheckKey.sElen)),
    .mov .rbp (.mem (hdr sMask))] : List Instr)),
  maskWords]

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs (
  [.block head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx,
    .block [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]] ++
  -- `p q = n`
  loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ Crt.eqCheck ++
  -- `n`
  copyOut [] aN ++
  -- `R² mod n`
  loadNum aM sD sDlen ++ accTop ++ reduce cntXR ++ copyOut skipW aR ++
  -- `R_p mod p` and `R_q mod q`
  loadNum aM sP sPlen ++ accPrime sPlen ++ reduce cntE ++ copyOut (skipW ++ skipW ++ primeW sPlen) aR ++
  loadNum aM sQ sQlen ++ accPrime sQlen ++ reduce cntE ++
    copyOut (skipW ++ skipW ++ primeW sPlen ++ skipW ++ primeW sQlen) aR ++
  maskOut ++
  [.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)])

/-- `vg_rsa_private_precompute`. -/
def code : Prog isa := .seq (.block (entry ++ invalid)) (.ite .ne failZ main)

end VG.Impl.Rsa.X86_64.PrivPre
