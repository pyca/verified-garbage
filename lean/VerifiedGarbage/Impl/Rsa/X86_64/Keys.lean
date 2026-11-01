module

public import VerifiedGarbage.Impl.Rsa.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Inv

/-!
# RSA private keys on x86-64: the shared routines and `vg_rsa_crt_values`

The working space is `vg_rsa_public`'s (`Impl/Bignum/X86_64.lean`): a header
of 32 words and arrays of `w + 2` words after it, array `j` at byte
`256 + 8 (w + 2) j`. Arrays 0 to 7 have their bases in the header, as
`vg_rsa_public`'s; the routines here compute every base from `rdi` and the
stride `8 (w + 2)` (in `r9`, from the header), so that they need no other
register from the header but `w` (in `r12`): their addresses and branches
depend only on `rdi`, `w` and the stride, all public.

* `divmod q r d t`: the remainder and the quotient of `[q]` by `[d]`
  (`w` words each), by `64 w` steps of bit-serial division: `([r], [q])`
  shifted left a bit, then `[t] = [r] - [d]` over `w + 1` words and `[r]`
  replaced by `[t]` and `[q]`'s low bit set if it does not borrow. `[r]`
  ends as the remainder and `[q]` as the quotient.
* `inverse u v x₂ m`: `[v] = gcd(a, m)` and `[x₂]` with `[x₂] a ≡ [v]
  (mod m)` for `a` in `[u]` and an odd `m` in `[m]`, by batches of divsteps
  at a width `n` read at run time (`inverseN`), in arrays of its own from
  16 on (see "The inverse" below).

`vg_rsa_crt_values(dp, dp_len, dq, dq_len, qinv, qinv_len, n, n_len, p,
p_len, q, q_len, d, d_len, scratch, scratch_len)`: the first six arguments
in registers, the others on the stack. `n` is checked as `vg_rsa_public`
checks it (it is public); then `p q = n` gives a mask, `qInv` is computed
by `inverse` (and'ing `gcd(q, p) = 1` into the mask), and `dP` and `dQ` by
`divmod` (with the divisor `p` or `q` with its low bit cleared: `p - 1` for
an odd `p`, which `p q = n` implies). Each result is written out masked.
`p q = n` is checked by `divmod` too, as `n mod p = 0`, `n / p = q` and `p`
odd.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.Keys

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-! ## Arrays by their index -/

/-- The header slot of the stride `8 (w + 2)`. -/
def sStride : Nat := sFn 12
/-- A header slot for the routines' own masks. -/
def sMo : Nat := sFn 13

/-- `w` into `r12` and the stride into `r9`. -/
def ws : List Instr := [.mov .r12 (.mem (hdr sW)), .mov .r9 (.mem (hdr sStride))]

/-- `mulBits` with `f` bits of fuel (`j ≤ f` suffices), by structural
recursion, which the kernel evaluates. -/
def mulBitsF (r : Reg) : Nat → Nat → List Instr
  | 0, _ => []
  | f + 1, j => if j < 2 then [] else
    mulBitsF r f (j / 2) ++ ([.alu .add r (.reg r)] : List Instr) ++
      (if j % 2 = 1 then ([.alu .add r (.reg .r9)] : List Instr) else [])

/-- `r := j · r9` for `j ≥ 1`, from `r = r9`, by the bits of `j` below its
top one, most significant first: `r := 2 r`, then `r := r + r9` if the bit
is set. -/
def mulBits (r : Reg) (j : Nat) : List Instr := mulBitsF r j j

/-- `rdi + 256 + j · r9` into `r` by `j` additions of `r9`. -/
def baseRep (j : Nat) (r : Reg) : List Instr :=
  ([.mov r (.reg .rdi), .alu .add r (.imm (BitVec.ofNat 32 hdrBytes))] : List Instr) ++ List.replicate j (.alu .add r (.reg .r9))

/-- The base of array `j` into `r`: `rdi + 256 + j · r9`, with `j · r9` by
`mulBits` (`r` and the flags only; `baseRep` for `j = 0`, or `r = rdi`,
which reads `rdi` first). -/
def base (j : Nat) (r : Reg) : List Instr :=
  if j = 0 ∨ r = .rdi then baseRep j r
  else ([.mov r (.reg .r9)] : List Instr) ++ mulBits r j ++
    ([.alu .add r (.reg .rdi), .alu .add r (.imm (BitVec.ofNat 32 hdrBytes))] : List Instr)

/-- `[j] := 0` (`w + 2` words). -/
def zeroA (j : Nat) : Prog isa := .seq (.block (ws ++ base j .r8)) zeroAccLoop

/-- `[o] := [a]` over `w` words. -/
def copyA (o a : Nat) : Prog isa := .seq (.block (ws ++ base a .rsi ++ base o .rbx)) copyWords

/-! ## Loops over the words -/

/-- `[rbx] := 2 [rbx] + c` with the carry chain in `rbp`. -/
def shlBody : List Instr :=
  [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.reg .rax), .store (ix .rbx .r14) .rax, cfToRbp]

/-- `[rsi] := [r8] - [r10]` with the borrow chain in `rbp` (`subMod`'s). -/
def subBody : List Instr :=
  [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), .store (ix .rsi .r14) .rax,
    cfToRbp]

/-- `[r8] := rbp ? [r8] : [rsi]`. -/
def selBody : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14)), .mov .rdx (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .rdx),
    .alu .and .rax (.reg .rbp), .alu .xor .rax (.reg .rdx), .store (ix .r8 .r14) .rax]

/-- `[rsi] := [r8] - ([r10] & r15)` with the borrow chain in `rbp`. -/
def subMBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), .mov .rdx (.mem (ix .r8 .r14)), cfFromRbp,
    .alu .sbb .rdx (.reg .rax), .store (ix .rsi .r14) .rdx, cfToRbp]

/-- `[rbx] := ([r10] & r15) + [r8]` with the carry chain in `rbp`
(`subModArr`'s second loop). -/
def addMBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), cfFromRbp, .alu .adc .rax (.mem (ix .r8 .r14)),
    .store (ix .rbx .r14) .rax, cfToRbp]

/-- `[rsi] := [r8] / 2`, word `i` from words `i` and `i + 1` of `[r8]` (the
low bit of word `i + 1` added as the top bit of word `i`). -/
def shrBody : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14)), .shift .shr .rax 1, .mov .rdx (.mem (ix .r8 .r14 8)), .alu .and .rdx (.imm 1),
    .shift .ror .rdx 1, .alu .add .rax (.reg .rdx), .store (ix .rsi .r14) .rax]

/-- `[rbx], [r10] := [r10], [rbx]` under the mask `r15`. -/
def cswapBody : List Instr :=
  [.mov .rax (.mem (ix .rbx .r14)), .mov .rdx (.mem (ix .r10 .r14)), .alu .xor .rax (.reg .rdx),
    .alu .and .rax (.reg .r15), .mov .rdx (.mem (ix .rbx .r14)), .alu .xor .rdx (.reg .rax),
    .store (ix .rbx .r14) .rdx, .mov .rdx (.mem (ix .r10 .r14)), .alu .xor .rdx (.reg .rax),
    .store (ix .r10 .r14) .rdx]

/-- `rbp |= [rbx] ^ [r10]`. -/
def xorBody : List Instr :=
  [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)]

/-! ## Division -/

/-- `([r], [q]) := 2 ([r], [q])`, `[r]` over `w + 1` words (`r12` left at
`w + 1`). -/
def divShiftP (iQ iR : Nat) : List (Prog isa) := [
  .block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base iQ .rbx),
  wordLoop 0 shlBody,
  .block (base iR .rbx ++ ([.alu .add .r12 (.imm 1)] : List Instr)),
  wordLoop 0 shlBody]

/-- `[t] := [r] - [d]` over `w + 1` words, then `[r] := [t]` if it does not
borrow, `rbp` the mask of the borrow. -/
def divSubP (iR iD iT : Nat) : List (Prog isa) := [
  .block (([.alu .sub .r12 (.imm 1), .mov32 .rbp (.imm 0)] : List Instr) ++ base iR .r8 ++ base iD .r10 ++ base iT .rsi),
  wordLoop 0 subBody,
  .block [.mov .rax (.mem (ix .r8 .r12)), cfFromRbp, .alu .sbb .rax (.imm 0), .store (ix .rsi .r12) .rax, cfToRbp,
    .alu .add .r12 (.imm 1)],
  wordLoop 0 selBody]

/-- `[q] += 1` if it did not borrow, `r12 := w`, and the step counter `r13`
against `r11`. -/
def divBitP (iQ : Nat) : List Instr :=
  ([.alu .sub .r12 (.imm 1), .mov .rax (.reg .rbp), .alu .add .rax (.imm 1)] : List Instr) ++ base iQ .rbx ++
    ([.mov .rdx (.mem (at0 .rbx)), .alu .add .rdx (.reg .rax), .store (at0 .rbx) .rdx,
      .alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r11)] : List Instr)

/-- One step of the division. -/
def divStep (iQ iR iD iT : Nat) : Prog isa := seqs (divShiftP iQ iR ++ (divSubP iR iD iT ++ [.block (divBitP iQ)]))

/-- `w` and the stride, `r8 := [r]`, `r11 := 64 w`, `r13 := 0`. -/
def divInit (iR : Nat) : List Instr :=
  ws ++ base iR .r8 ++ ([.mov .r11 (.reg .r12)] : List Instr) ++ List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
    ([.mov32 .r13 (.imm 0)] : List Instr)

/-- `[r] := [q] mod [d]` and `[q] := [q] / [d]`, `[t]` working space:
`64 w` steps. -/
def divmod (iQ iR iD iT : Nat) : Prog isa :=
  seqs [.block (divInit iR), zeroAccLoop, .loop (divStep iQ iR iD iT) .ne]

/-- The step counter `r13` against `r11`. -/
def countP : List Instr := [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r11)]

/-! ## Masks -/

/-- `rbp = 0` iff `[a] = [b]` over `w` words. -/
def eqA (a b : Nat) : List (Prog isa) :=
  [.block (ws ++ base a .rbx ++ base b .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr)), wordLoop 0 xorBody]

/-- `[j] := 1`, for `[j] = 0`. -/
def setOneA (j : Nat) : List Instr := ws ++ base j .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)

/-- The low word of `[j]` minus one (`[j] - 1` for a `[j]` whose low word
is not zero). -/
def decA (j : Nat) : List Instr :=
  ws ++ base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .sub .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)

/-! ## The inverse: batches of divsteps

`inverse u v x₂ m` (`n` in `r13`, `w` and the stride from `ws`): from `a` in
`[u]` and the odd `m` in `[m]`, both below `2^(64 n)`, `[v] = gcd(a, m)` and
`[x₂] a ≡ [v] (mod m)`, `[x₂] < m`, by Bernstein–Yang divsteps in batches of
59 on the low words (`pchunk`, as `Impl/Weierstrass/X86_64/Inv.lean`'s) at
the width `n` read at run time: `f = m`, `g = a` or `a + m` if `a` is even
(odd, so its first divstep swaps it below `m` if it is larger), `n + 1`
words each in two's complement, `(a, b) = (0, 1)` reduced by one word of
Montgomery reduction per batch (`mred`) modulo `m` with its low bit set (so
that the batches run on an odd modulus whatever `m` is), `3 n + 2` batches (`177 n + 118`
divsteps, enough for numbers below `2^(64 n + 32)`). Then `g = 0` and
`f = ±gcd`, `x₂ = ±a 2^(5 B) mod m` by `5 B` modular doublings, and
`v = |f|`.

Its working space is arrays of its own, from 16 on: a window (`aWin`, three
arrays), `f`, `g`, `a`, `b`, a product `t` (`n + 2` words), a staging array
and `m` (`aP`, its words above `n` zero). In a batch `rdi` points at the
window, whose words are the low words of `f` and `g` and the chunks'
temporary (at 0, 8, 16: `pchunk`'s), `d`, the matrix `u, v, q, r`, the two
masks of the coefficients' signs and `-m⁻¹ mod 2^64`; the other arrays'
bases are `rdi` plus multiples of the stride in `r9`. `n` is in `r15`, the
count of batches in `rsi`, and the stride in `r14` across the divsteps,
which write `r9`–`r13`. Every branch and address depends only on `rdi`,
the stride, `n` and the counts. -/

namespace Inv

open VG.Impl.Weierstrass.X86_64 (pchunk)

/-- The arrays (`aWin` is three: `16`–`18`). -/
def aWin : Nat := 16
def aF : Nat := 19
def aG : Nat := 20
def aA : Nat := 21
def aB : Nat := 22
def aT : Nat := 23
def aS : Nat := 24
def aP : Nat := 25

/-- The window's slots (bytes). -/
def oD : Nat := 24
def oU : Nat := 32
def oV : Nat := 40
def oQ : Nat := 48
def oR : Nat := 56
def oMu : Nat := 64
def oMv : Nat := 72
def oMi : Nat := 80

/-- A word of the window. -/
def wm (d : Nat) : MemOp := { base := .rdi, disp := d }

/-- `r := rdi + k r9`: array `16 + k`'s base, from the window's. -/
def wa (k : Nat) (r : Reg) : List Instr :=
  ([.mov r (.reg .rdi)] : List Instr) ++ List.replicate k (.alu .add r (.reg .r9))

/-! ### The start (`rdi` the working space's base) -/

/-- `g := a + (m if a is even)` over `w + 1` words, from `a` in `aT` and `m` in `aP`. -/
def gInit : List (Prog isa) := [
  .block (ws ++ base aT .r8 ++ ([.mov .rax (.mem (at0 .r8)), .alu .and .rax (.imm 1), .alu .sub .rax (.imm 1),
    .mov .r15 (.reg .rax), .alu .add .r12 (.imm 1), .mov32 .rbp (.imm 0)] : List Instr) ++ base aG .rbx ++
    base aP .r10),
  wordLoop 0 addMBody]

/-- `d = 1` and `-m⁻¹ mod 2^64` into the window, `r15 := n`, the count of
batches `3 n + 2` into `rsi`, and `rdi` to the window. -/
def setup : List Instr :=
  ws ++ base aP .r8 ++ ([.mov .rbx (.mem (at0 .r8))] : List Instr) ++ minv ++ base aWin .r8 ++
  ([.store { base := .r8, disp := oMi } .r15, .mov32 .rax (.imm 1), .store { base := .r8, disp := oD } .rax,
    .mov .r15 (.reg .r13), .mov .rsi (.reg .r13), .alu .add .rsi (.reg .r13), .alu .add .rsi (.reg .r13),
    .alu .add .rsi (.imm 2)] : List Instr) ++ base aWin .rdi

/-- `m`'s low bit set in `aP`: an odd modulus for the batches whatever `m` is
(`m` itself when it is odd). -/
def setOdd : List Instr :=
  ws ++ base aP .r8 ++ ([.mov .rax (.mem (at0 .r8)), .shift .shr .rax 1, .alu .add .rax (.reg .rax),
    .alu .add .rax (.imm 1), .store (at0 .r8) .rax] : List Instr)

/-- The start: the arrays zeroed, `m` into `aP` (made odd) and `f`, `a` into
`aT`, `g`, `(a, b) = (0, 1)`, then `setup`. -/
def start (iU iM : Nat) : List (Prog isa) :=
  [zeroA aF, zeroA aG, zeroA aA, zeroA aB, zeroA aT, zeroA aS, zeroA aP, copyA aP iM, .block setOdd, copyA aF aP,
    copyA aT iU] ++
  gInit ++ [.block (setOneA aB), .block setup]

/-! ### A batch (`rdi` the window, `r9` the stride, `r15` `n`) -/

/-- The low words of `f` and `g` into the window, `~d` into `rbx`, the stride into `r14`. -/
def bStart : List Instr :=
  wa 3 .rax ++ ([.mov .rax (.mem (at0 .rax)), .store (wm 0) .rax] : List Instr) ++ wa 4 .rax ++
  ([.mov .rax (.mem (at0 .rax)), .store (wm 8) .rax, .mov .rbx (.mem (wm oD)), .alu .xor .rbx (.imm (-1)),
    .mov .r14 (.reg .r9)] : List Instr)

/-- 59 divsteps: `d` and the matrix in `rbx`, `r9`–`r12`. -/
def bWords : List Instr :=
  pchunk 0 15 true false ++ pchunk 0 15 false false ++ pchunk 0 15 false false ++ pchunk 0 14 false true ++
    ([.alu .xor .rbx (.imm (-1))] : List Instr)

/-- `d` and the matrix into the window, the stride back into `r9`, `r12 := n + 1`. -/
def bSave : List Instr :=
  [.store (wm oD) .rbx, .store (wm oU) .r9, .store (wm oV) .r10, .store (wm oQ) .r11, .store (wm oR) .r12,
    .mov .r9 (.reg .r14), .mov .r12 (.reg .r15), .alu .add .r12 (.imm 1)]

/-- `a = |c|` for the coefficient at `[c]`, and the mask of its sign into `[m]`. -/
def absM (c m : Nat) (a : Reg) : List Instr :=
  [.mov a (.mem (wm c)), .mov .rax (.reg a), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
    .store (wm m) .rdx, .alu .xor a (.reg .rdx), .alu .sub a (.reg .rdx)]

/-- Column `i` (`r14`) of `[r11] = u [rbx] + v [r10]`: the two products of
`|u|` (`rcx`) and `|v|` (`rbp`) by the words complemented under the masks
added to the accumulator `r8`, `r13`, whose low word is stored. -/
def linBody : List Instr :=
  [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (wm oMu)), .mul .rcx, .alu .add .r8 (.reg .rax),
    .alu .adc .r13 (.reg .rdx), .mov .rax (.mem (ix .r10 .r14)), .alu .xor .rax (.mem (wm oMv)), .mul .rbp,
    .alu .add .r8 (.reg .rax), .alu .adc .r13 (.reg .rdx), .store (ix .r11 .r14) .r8, .mov .r8 (.reg .r13),
    .mov32 .r13 (.imm 0)]

/-- `[t] = c [16 + kX] + c' [16 + kY]` for the coefficients at `[cu]`, `[cv]`,
over `n + 1` words (`r12`), modulo `2^(64 (n + 1))`. -/
def lin (cu cv kX kY : Nat) : List (Prog isa) := [
  .block (absM cu oMu .rcx ++ absM cv oMv .rbp ++
    ([.mov .r8 (.reg .rcx), .alu .and .r8 (.mem (wm oMu)), .mov .rax (.reg .rbp), .alu .and .rax (.mem (wm oMv)),
      .alu .add .r8 (.reg .rax), .mov32 .r13 (.imm 0)] : List Instr) ++ wa kX .rbx ++ wa kY .r10 ++ wa 7 .r11),
  wordLoop 0 linBody]

/-- Word `i` (`r14`) of `[r10] = [rbx] / 2^59`, from words `i` and `i + 1`. -/
def shrBody : List Instr :=
  [.mov .rax (.mem (ix .rbx .r14)), .shift .shr .rax 59, .mov .r8 (.mem (ix .rbx .r14 8)), .shift .shl .r8 5,
    .alu .add .rax (.reg .r8), .store (ix .r10 .r14) .rax]

/-- `[16 + kD] = [t] / 2^59`, arithmetic, `n + 1` words: `n` from pairs of
words, then the top one from its sign. -/
def shr (kD : Nat) : List (Prog isa) := [
  .block (wa 7 .rbx ++ wa kD .r10 ++ ([.mov .r12 (.reg .r15)] : List Instr)),
  wordLoop 0 shrBody,
  .block [.mov .rdx (.mem (ix .rbx .r14)), .mov .r8 (.reg .rdx), .shift .shr .r8 63, .mov32 .rax (.imm 0),
    .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax), .mov .rax (.reg .rdx), .shift .shr .rax 59, .shift .shl .r8 5,
    .alu .add .rax (.reg .r8), .store (ix .r10 .r14) .rax, .alu .add .r12 (.imm 1)]]

/-- `[16 + kD] = ([t] + k m) / 2^64` (`n + 1` words), for `k = [t]₀ (-m⁻¹)
mod 2^64` and `[t]` sign-extended to `n + 2` words: `[t]`'s word `n + 1`
zeroed, `k m` added by `mulAddRow` (with `m`'s base in `r9`, the stride
kept in `r13`), and the mask of `[t]`'s sign (kept at `oMu`) added to its
word `n + 1`; then its words `1 … n + 1`. -/
def mred (kD : Nat) : List (Prog isa) := [
  .block (wa 7 .r8 ++ wa 9 .r10 ++ wa kD .r11 ++
    ([.mov .rax (.mem (at0 .r8)), .mov .rcx (.mem (wm oMi)), .mul .rcx, .mov .rcx (.reg .rax),
      .mov .rax (.mem (ix .r8 .r15)), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
      .store (wm oMu) .rdx, .mov32 .rax (.imm 0), .store (ix .r8 .r15 8) .rax, .mov .r13 (.reg .r9),
      .mov .r9 (.reg .r10), .mov .r12 (.reg .r15)] : List Instr)),
  mulAddRow,
  .block [.mov .r9 (.reg .r13), .mov .rax (.mem (ix .r8 .r15 8)), .alu .add .rax (.mem (wm oMu)),
    .store (ix .r8 .r15 8) .rax, .alu .add .r12 (.imm 1)],
  wordLoop 0 [.mov .rax (.mem (ix .r8 .r14 8)), .store (ix .r11 .r14) .rax]]

/-- `[16 + kD] = [16 + kS]`, `n + 1` words. -/
def copyW (kS kD : Nat) : List (Prog isa) :=
  [.block (wa kS .rbx ++ wa kD .r10), wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .store (ix .r10 .r14) .rax]]

/-- A batch: the divsteps, `(f, g) := (u f + v g, q f + r g) / 2^59` (`f`
staged), `(a, b)` likewise by `mred`, and the count less one. -/
def batch : Prog isa := seqs ([.block (bStart ++ bWords ++ bSave)] ++ lin oU oV 3 4 ++ shr 8 ++ lin oQ oR 3 4 ++
  shr 4 ++ copyW 8 3 ++ lin oU oV 5 6 ++ mred 8 ++ lin oQ oR 5 6 ++ mred 6 ++ copyW 8 5 ++
  [.block [.alu .sub .rsi (.imm 1)]])

/-! ### The end (`rdi` the working space's base again) -/

/-- `rdi` back to the working space's base, `r13 := n`, `r12 := n + 1`. -/
def unwin : List Instr :=
  ([.alu .sub .rdi (.imm (BitVec.ofNat 32 hdrBytes))] : List Instr) ++ List.replicate aWin (.alu .sub .rdi (.reg .r9)) ++
  ([.mov .r13 (.reg .r15)] : List Instr)

/-- `r12 := n + 1`. -/
def countN : List Instr := [.mov .r12 (.reg .r13), .alu .add .r12 (.imm 1)]

/-- `rbp` the mask of `[j] ≥ 0` (its word `n`'s top bit clear). -/
def nonNeg (j : Nat) : List Instr :=
  base j .rbx ++ ([.mov .rax (.mem (ix .rbx .r13)), .shift .shr .rax 63, .alu .sub .rax (.imm 1),
    .mov .rbp (.reg .rax)] : List Instr)

/-- `[t] := [t] - m` if that does not borrow (`n + 1` words). -/
def csubT : List (Prog isa) :=
  [.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aT .r8 ++ base aP .r10 ++ base aS .rsi), wordLoop 0 subBody,
    wordLoop 0 selBody]

/-- `[t] := 2 [t] mod m`. -/
def dbl : Prog isa :=
  seqs ([.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aT .rbx), wordLoop 0 shlBody] ++ csubT ++
    [.block [.alu .sub .r11 (.imm 1)]])

/-- The end: `t := a mod m` (`a + m` if `a < 0`, less `m` if not below
it), `t := m - t` if `f < 0`, `5 B` doublings and a last subtraction, so
`t = ±a 2^(5 B) mod m`; `f := |f|`; then `[v] = f` and `[x₂] = t`. -/
def finish (iV iX₂ : Nat) : List (Prog isa) := [
  .block unwin, zeroA aT,
  .block (countN ++ base aA .r8 ++ ([.mov .rax (.mem (ix .r8 .r13)), .shift .shr .rax 63, .mov32 .r15 (.imm 0),
    .alu .sub .r15 (.reg .rax), .mov32 .rbp (.imm 0)] : List Instr) ++ base aT .rbx ++ base aP .r10),
  wordLoop 0 addMBody] ++ csubT ++ [
  .block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aP .r8 ++ base aT .r10 ++ base aS .rsi), wordLoop 0 subBody,
  .block (nonNeg aF ++ base aT .r8 ++ base aS .rsi), wordLoop 0 selBody,
  .block [.mov .r11 (.reg .r13), .shift .shl .r11 4, .alu .sub .r11 (.reg .r13), .alu .add .r11 (.imm 10)],
  .loop dbl .ne] ++ csubT ++ [
  zeroA aA,
  .block (countN ++ ([.mov32 .rbp (.imm 0)] : List Instr) ++ base aA .r8 ++ base aF .r10 ++ base aS .rsi),
  wordLoop 0 subBody,
  .block (nonNeg aF ++ base aF .r8 ++ base aS .rsi), wordLoop 0 selBody,
  copyA iV aF, copyA iX₂ aT]

end Inv

/-- The inverse at the width `n` in `r13`. -/
def inverseN (iU iV iX₂ iM : Nat) : Prog isa :=
  seqs (Inv.start iU iM ++ [.loop Inv.batch .ne] ++ Inv.finish iV iX₂)

/-- The inverse at the width `w`. -/
def inverse (iU iV iX₂ iM : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.mov .r13 (.reg .r12)] : List Instr))) (inverseN iU iV iX₂ iM)

/-! ## Bytes -/

/-- `[j] := ` the number of the bytes whose pointer and length are in the
header slots `sPtr` and `sLen`. -/
def loadA (j sPtr sLen : Nat) : List (Prog isa) :=
  [zeroA j, .block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] : List Instr)), loadBE]

/-- `[j]` masked by the header slot `sMsk`, to the bytes whose pointer and
length are in the header slots `sPtr` and `sLen`. -/
def storeA (j sPtr sLen sMsk : Nat) : List (Prog isa) :=
  [.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)),
    .mov .r15 (.mem (hdr sMsk))] : List Instr)), storeBE]

/-- Zeros to the bytes whose pointer and length are in the header slots
`sPtr` and `sLen` (at least one). -/
def zeroOut (sPtr sLen : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)), .mov32 .rax (.imm 0)])
    (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)

/-- The mask's low bit returned, and the saved registers restored. -/
def retMask : List Instr := ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit

/-! ## `vg_rsa_crt_values` -/

namespace CrtValues

/-- Header slots: `n`'s pointer and length in `vg_rsa_public`'s `sN` and
`sK`, the mask in its `sMask`. -/
def sDp : Nat := sFn 0
def sDq : Nat := sFn 3
def sQi : Nat := sFn 4
def sPl : Nat := sFn 5
def sQl : Nat := sFn 7
def sP : Nat := sFn 8
def sQ : Nat := sFn 9
def sD : Nat := sFn 10
def sDl : Nat := sFn 11

/-- The arrays: `n` (0), `p` (1), `divmod`'s quotient and remainder or
`inverse`'s `u` and `v` (2 and 3), `q` (4), `d` (5), `inverse`'s `x₁` and
`x₂` (6 and 7), the working array (8) and a constant or the divisor (9,
`aC`). -/
def aP : Nat := 1
def aQ : Nat := 4
def aD : Nat := 5
def aU : Nat := 2
def aV : Nat := 3
def aX₁ : Nat := 6
def aX₂ : Nat := 7
def aT : Nat := 8

/-- The stack argument `i` (from 1). -/
def stk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`. `dp_len` and `dq_len` are `p_len` and
`q_len`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem (stk 9))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  ([.store { base := .r11, disp := 8 * sDp } .rdi, .store { base := .r11, disp := 8 * sPl } .rsi,
    .store { base := .r11, disp := 8 * sDq } .rdx, .store { base := .r11, disp := 8 * sQl } .rcx,
    .store { base := .r11, disp := 8 * sQi } .r8,
    .mov .rax (.mem (stk 1)), .store { base := .r11, disp := 8 * sN } .rax,
    .mov .rax (.mem (stk 2)), .store { base := .r11, disp := 8 * sK } .rax,
    .mov .rax (.mem (stk 3)), .store { base := .r11, disp := 8 * sP } .rax,
    .mov .rax (.mem (stk 5)), .store { base := .r11, disp := 8 * sQ } .rax,
    .mov .rax (.mem (stk 7)), .store { base := .r11, disp := 8 * sD } .rax,
    .mov .rax (.mem (stk 8)), .store { base := .r11, disp := 8 * sDl } .rax, .mov .rdi (.reg .r11)] : List Instr)

/-- Zeros to `dp`, `dq` and `qinv`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut sDp sPl, zeroOut sDq sQl, zeroOut sQi sPl, .block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)]

/-- `w`, the arrays' bases and the stride, and the mask all ones. -/
def head : List Instr :=
  ([.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7), .shift .shr .r12 3,
    .store (hdr sW) .r12] : List Instr) ++ setBases ++
  ([.mov .rax (.reg .r12), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .store (hdr sStride) .rax, .mov .rax (.imm (BitVec.ofInt 32 (-1))),
    .store (hdr sMask) .rax] : List Instr)

/-- The constant array `aC` (9): zero, or one. -/
def aC : Nat := 9

/-- The mask of `rbp = 0` and'ed into `sMask`. -/
def andZero : List Instr :=
  [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .alu .and .rbp (.mem (hdr sMask)), .store (hdr sMask) .rbp]

/-- The mask of `[j]` odd and'ed into `sMask`. -/
def andOdd (j : Nat) : List Instr :=
  ws ++ base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .alu .and .rdx (.mem (hdr sMask)), .store (hdr sMask) .rdx] : List Instr)

/-- The mask of `p q = n` and'ed into `sMask`, as `n mod p = 0`,
`n / p = q` and `p` odd (which `p q = n` implies, `n` being odd). -/
def pqCheck : List (Prog isa) :=
  [zeroA aU, copyA aU aN, divmod aU aV aP aT] ++ eqA aU aQ ++ [.block andZero, zeroA aC] ++ eqA aV aC ++
    [.block andZero, .block (andOdd aP)]

def invPart : List (Prog isa) :=
  ([inverse aQ aV aX₂ aP, zeroA aC, .block (setOneA aC)] ++ (eqA aV aC ++ [.block andZero]))

/-- `[aC] := [j] - 1` (for an odd `[j]`, whose low word is not zero), then `[aU] := d`. -/
def divisor (j : Nat) : List (Prog isa) :=
  [zeroA aC, copyA aC j, .block (decA aC), zeroA aU, copyA aU aD]

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([
  .block head] ++ loadA aN sN sK ++ loadA aP sP sPl ++ loadA aQ sQ sQl ++ loadA aD sD sDl ++ pqCheck ++ invPart ++
  -- `dP = d mod (p - 1)` into `aX₁` and `dQ = d mod (q - 1)` in `aV`.
  divisor aP ++ [divmod aU aV aC aT, zeroA aX₁, copyA aX₁ aV] ++ divisor aQ ++ [divmod aU aV aC aT] ++
  storeA aX₂ sQi sPl sMask ++ storeA aX₁ sDp sPl sMask ++ storeA aV sDq sQl sMask ++
  [.block retMask])

/-- `vg_rsa_crt_values`. -/
def code : Prog isa :=
  .seq (.block (entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid)) (.ite .ne fail main)

end CrtValues

end VG.Impl.Rsa.X86_64.Keys
