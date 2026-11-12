module

public import VerifiedGarbage.Impl.Rsa.X86_64
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Impl.Rsa.X86_64.WordReduce
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
* `gcdW u v m`: `[v] = gcd(a, m)` alone, the inverse's batches without
  `(a, b)` and its end without `[x₂]` (`gcdN` at the width `n` in `r13`).

`vg_rsa_crt_values(dp, dp_len, dq, dq_len, qinv, qinv_len, n, n_len, p,
p_len, q, q_len, d, d_len, scratch, scratch_len)`: the first six arguments
in registers, the others on the stack. `n` is checked as `vg_rsa_public`
checks it (it is public); then `p q = n` gives a mask, `qInv` is computed
by `inverseN` at the primes' width `⌈max(p_len, q_len) / 8⌉` (and'ing
`gcd(q, p) = 1` into the mask), and `dP` and `dQ` by
`divmod` (with the divisor `p` or `q` with its low bit cleared: `p - 1` for
an odd `p`, which `p q = n` implies). Where the public guard of
`wordChoice` holds (balanced full-word factors and `n`'s top bit set), the
remainders are `WordDivide`'s, and the inverse leaves out its `2^(5 B)`
doublings (`inverseNS`), which `qTail` applies instead by one `WordDivide`
reduction modulo `p`. Each result is written out masked.
`p q = n` is checked by multiplying the factors into two contiguous
arrays and comparing the full product with `n`.
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

`inverse u v x₂ m` (`n` in `r13`, `w` and the stride from `ws`): from `a`,
the low `n` words of `[u]`, and the odd `m`, those of `[m]` (it reads no
others), `[v] = gcd(a, m)` and
`[x₂] a ≡ [v] (mod m)`, `[x₂] < m`, by Bernstein–Yang divsteps in batches of
59 on the low words (`pchunk`, as `Impl/Weierstrass/X86_64/Inv.lean`'s) at
the width `n` read at run time: `f = m`, `g = a` or `a + m` if `a` is even
(odd, so its first divstep swaps it below `m` if it is larger), `n + 1`
words each in two's complement, `(a, b) = (0, 1)` reduced by one word of
Montgomery reduction per batch modulo `m` with its low bit set (so
that the batches run on an odd modulus whatever `m` is), `3 n + 2` batches (`177 n + 118`
divsteps, enough for numbers below `2^(64 n + 32)`). Then `g = 0` and
`f = ±gcd`, `x₂ = ±a 2^(5 B) mod m` by `5 B` modular doublings, and
`v = |f|`.

Its working space is arrays of its own, from 16 on: a window (`aWin`, three
arrays), `f`, `g`, `a`, `b`, the end's temporaries `t` and `s`, and `m`
(`aP`, its words above `n` zero). In a batch `rdi` points at the window,
whose words are the low words of `f` and `g` and the chunks' temporary (at
0, 8, 16: `pchunk`'s), `d`, the matrix `u, v, q, r`, the masks of the
coefficients' signs and `-m⁻¹ mod 2^64`; the other arrays' bases are `rdi`
plus multiples of the stride in `r9`. A batch updates `(f, g)` and then
`(a, b)` a word at a time, each pair in place in one pass (`fgRow`,
`abRow`). `n` is in `r15` (the end of a row while it runs), the count of
batches in `rsi`, and the stride in `r14` across the divsteps, which write
`r9`–`r13`. Every branch and address depends only on `rdi`, the stride, `n`
and the counts, all in registers. -/

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

/-- `r12 := w` from the stride in `r9` (`8 (w + 2)`), rather than from the
header as `ws` does: the inverse reads no memory for its counts, so a single
check of its taint covers it. -/
def wsR : List Instr := [.mov .r12 (.reg .r9), .shift .shr .r12 3, .alu .sub .r12 (.imm 2)]

/-- `zeroA`, with `wsR`. -/
def zeroI (j : Nat) : Prog isa := .seq (.block (wsR ++ base j .r8)) zeroAccLoop

/-- `copyA`, with `wsR`. -/
def copyI (o a : Nat) : Prog isa := .seq (.block (wsR ++ base a .rsi ++ base o .rbx)) copyWords

/-- `copyA` of the low `n` words (`r13`): the inputs, which the inverse
reads at its width only, whatever their words above it. -/
def copyN (o a : Nat) : Prog isa :=
  .seq (.block (([.mov .r12 (.reg .r13)] : List Instr) ++ base a .rsi ++ base o .rbx)) copyWords

/-- `setOneA`, with `wsR`. -/
def setOneI (j : Nat) : List Instr :=
  wsR ++ base j .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)

/-- `r := rdi + k r9`: array `16 + k`'s base, from the window's. -/
def wa (k : Nat) (r : Reg) : List Instr :=
  ([.mov r (.reg .rdi)] : List Instr) ++ List.replicate k (.alu .add r (.reg .r9))

/-! ### The start (`rdi` the working space's base) -/

/-- `g := a + (m if a is even)` over `w + 1` words, from `a` in `aT` and `m` in `aP`. -/
def gInit : List (Prog isa) := [
  .block (wsR ++ base aT .r8 ++ ([.mov .rax (.mem (at0 .r8)), .alu .and .rax (.imm 1), .alu .sub .rax (.imm 1),
    .mov .r15 (.reg .rax), .alu .add .r12 (.imm 1), .mov32 .rbp (.imm 0)] : List Instr) ++ base aG .rbx ++
    base aP .r10),
  wordLoop 0 addMBody]

/-- `d = 1` and `-m⁻¹ mod 2^64` into the window, `r15 := n`, the count of
batches `3 n + 2` into `rsi`, and `rdi` to the window. -/
def setup : List Instr :=
  wsR ++ base aP .r8 ++ ([.mov .rbx (.mem (at0 .r8))] : List Instr) ++ minv ++ base aWin .r8 ++
  ([.store { base := .r8, disp := oMi } .r15, .mov32 .rax (.imm 1), .store { base := .r8, disp := oD } .rax,
    .mov .r15 (.reg .r13), .mov .rsi (.reg .r13), .alu .add .rsi (.reg .r13), .alu .add .rsi (.reg .r13),
    .alu .add .rsi (.imm 2)] : List Instr) ++ base aWin .rdi

/-- `m`'s low bit set in `aP`: an odd modulus for the batches whatever `m` is
(`m` itself when it is odd). -/
def setOdd : List Instr :=
  wsR ++ base aP .r8 ++ ([.mov .rax (.mem (at0 .r8)), .shift .shr .rax 1, .alu .add .rax (.reg .rax),
    .alu .add .rax (.imm 1), .store (at0 .r8) .rax] : List Instr)

/-- The start: the arrays zeroed, `m`'s low `n` words into `aP` (made odd)
and `f`, `a`'s into `aT`, `g`, `(a, b) = (0, 1)`, then `setup`. -/
def start (iU iM : Nat) : List (Prog isa) :=
  [zeroI aF, zeroI aG, zeroI aA, zeroI aB, zeroI aT, zeroI aS, zeroI aP, copyN aP iM, .block setOdd, copyI aF aP,
    copyN aT iU] ++
  gInit ++ [.block (setOneI aB), .block setup]

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

/-- The slots of `q`'s and `r`'s masks and of the factors `k` of `m` (the chunks' temporary words
and a free word, which the updates use after the divsteps). -/
def oMq : Nat := 0
def oMr : Nat := 8
def oKd : Nat := 16
def oKe : Nat := 88

/-- `[c] := |c|` and the mask of its sign into `[m]`. -/
def absS (c m : Nat) : List Instr :=
  [.mov .rcx (.mem (wm c)), .mov .rax (.reg .rcx), .shift .shr .rax 63, .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .store (wm m) .rdx, .alu .xor .rcx (.reg .rdx), .alu .sub .rcx (.reg .rdx),
    .store (wm c) .rcx]

/-- Word `j` of the first row's input (`r8`) and of the second's (`r8 + r9`), and of `m`
(`r8 + 4 r9`). -/
def px (d : Int) : MemOp := { base := .r8, disp := d }
def py (d : Int) : MemOp := { base := .r8, index := some .r9, scale := 1, disp := d }
def pm (d : Int) : MemOp := { base := .r8, index := some .r9, scale := 4, disp := d }

/-- A factor: in a register, or in its slot (loaded into `rdx`). -/
inductive Co | reg (r : Reg) | slot (c : Nat)

/-- `rdx:rax := rax · c`. -/
def mulCo : Co → List Instr
  | .reg r => [.mul r]
  | .slot c => [.mov .rdx (.mem (wm c)), .mul .rdx]

/-- `lo:hi += |c| (x ^ mask)`. -/
def term2 (x : MemOp) (c : Co) (m : Nat) (lo hi : Reg) : List Instr :=
  [.mov .rax (.mem x), .alu .xor .rax (.mem (wm m))] ++ mulCo c ++
    [.alu .add lo (.reg .rax), .alu .adc hi (.reg .rdx)]

/-- `lo:mid:top += |c| (x ^ mask)`. -/
def term3 (x : MemOp) (c : Co) (m : Nat) (lo mid top : Reg) : List Instr :=
  [.mov .rax (.mem x), .alu .xor .rax (.mem (wm m))] ++ mulCo c ++
    [.alu .add lo (.reg .rax), .alu .adc mid (.reg .rdx), .alu .adc top (.imm 0)]

/-- `lo:mid:top += k m_j`. -/
def termM (k : Co) (lo mid top : Reg) : List Instr :=
  [.mov .rax (.mem (pm 0))] ++ mulCo k ++ [.alu .add lo (.reg .rax), .alu .adc mid (.reg .rdx), .alu .adc top (.imm 0)]

/-- `lo := (|c| & mc) + (|c'| & mc')`: the ones of the complements. -/
def ones (cu mu cv mv : Nat) (lo : Reg) : List Instr :=
  [.mov lo (.mem (wm cu)), .alu .and lo (.mem (wm mu)), .mov .rax (.mem (wm cv)), .alu .and .rax (.mem (wm mv)),
    .alu .add lo (.reg .rax)]

/-- `r8` to word 0 of array `16 + k`, `r15` (`n`) to its word `n + 1`. -/
def rowStart (k : Nat) : List Instr :=
  wa k .r8 ++ ([.alu .add .r15 (.imm 1), .shift .shl .r15 3, .alu .add .r15 (.reg .r8)] : List Instr)

/-- `r15` back to `n`, from the end of array `16 + k`'s words. -/
def rowEnd (k : Nat) : List Instr :=
  wa k .rax ++ ([.alu .sub .r15 (.reg .rax), .shift .shr .r15 3, .alu .sub .r15 (.imm 1)] : List Instr)

/-- The previous word's top bits (`prev`) and this one's low (`lo`) into `dst`, `lo` kept in
`prev`, the accumulator down a word. -/
def outS (prev lo hi : Reg) (dst : MemOp) : List Instr :=
  [.mov .rax (.reg prev), .shift .shr .rax 59, .mov prev (.reg lo), .shift .shl lo 5, .alu .add .rax (.reg lo),
    .store dst .rax, .mov lo (.reg hi), .mov32 hi (.imm 0)]

/-- The last word: `prev`'s top bits and its sign's. -/
def outTop (prev : Reg) (dst : MemOp) : List Instr :=
  [.mov .rax (.reg prev), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .shift .shl .rdx 5,
    .mov .rax (.reg prev), .shift .shr .rax 59, .alu .add .rax (.reg .rdx), .store dst .rax]

/-- The step to the next word, and the end. -/
def next : List Instr := [.alu .add .r8 (.imm 8), .alu .cmp .r8 (.reg .r15)]

/-- `(f, g) := (u f + v g, q f + r g) / 2^59` in place, a word at a time: `r10:r11` and
`r12:r13` the sums, `rbx` and `rbp` their previous low words, `|u|` and `|v|` in `rcx`
and `r14`. -/
def fgCol : List Instr :=
  term2 (px 0) (.reg .rcx) oMu .r10 .r11 ++ term2 (py 0) (.reg .r14) oMv .r10 .r11 ++
    term2 (px 0) (.slot oQ) oMq .r12 .r13 ++ term2 (py 0) (.slot oR) oMr .r12 .r13

def fgRow : List (Prog isa) := [
  .block (rowStart 3 ++ ([.mov .rcx (.mem (wm oU)), .mov .r14 (.mem (wm oV))] : List Instr) ++
    ones oU oMu oV oMv .r10 ++ ([.mov32 .r11 (.imm 0)] : List Instr) ++
    ones oQ oMq oR oMr .r12 ++ ([.mov32 .r13 (.imm 0)] : List Instr) ++ fgCol ++
    ([.mov .rbx (.reg .r10), .mov .r10 (.reg .r11), .mov32 .r11 (.imm 0), .mov .rbp (.reg .r12),
      .mov .r12 (.reg .r13), .mov32 .r13 (.imm 0), .alu .add .r8 (.imm 8)] : List Instr)),
  .loop (.block (fgCol ++ outS .rbx .r10 .r11 (px (-8)) ++ outS .rbp .r12 .r13 (py (-8)) ++ next)) .ne,
  .block (outTop .rbx (px (-8)) ++ outTop .rbp (py (-8)) ++ rowEnd 3)]

/-- The sign word of `x` into `rdx`. -/
def signX (x : MemOp) : List Instr :=
  [.mov .rax (.mem x), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax)]

/-- `lo:mid:top += |c| (rdx ^ mask)`, `|c|` in `rcx` (which it overwrites). -/
def termR (c m : Nat) (lo mid top : Reg) : List Instr :=
  [.mov .rax (.reg .rdx), .alu .xor .rax (.mem (wm m)), .mov .rcx (.mem (wm c)), .mul .rcx,
    .alu .add lo (.reg .rax), .alu .adc mid (.reg .rdx), .alu .adc top (.imm 0)]

def shift3 (lo mid top : Reg) : List Instr := [.mov lo (.reg mid), .mov mid (.reg top), .mov32 top (.imm 0)]

/-- `k := lo (-m⁻¹) mod 2^64` into the slot `o`, then `lo:mid:top += k m₀`. -/
def kOf (o : Nat) (lo mid top : Reg) : List Instr :=
  [.mov .rax (.reg lo), .mov .rdx (.mem (wm oMi)), .mul .rdx, .store (wm o) .rax] ++ termM (.slot o) lo mid top

/-- `(a, b) := ((u a + v b + k m) / 2^64, (q a + r b + k' m) / 2^64)` in place: `r10:r11:r12`
and `r13:r14:rbx` the sums, `|u|` and `|v|` in `rcx` and `rbp`. -/
def abCol : List Instr :=
  term3 (px 0) (.reg .rcx) oMu .r10 .r11 .r12 ++ term3 (py 0) (.reg .rbp) oMv .r10 .r11 .r12 ++
    termM (.slot oKd) .r10 .r11 .r12 ++
    term3 (px 0) (.slot oQ) oMq .r13 .r14 .rbx ++ term3 (py 0) (.slot oR) oMr .r13 .r14 .rbx ++
    termM (.slot oKe) .r13 .r14 .rbx

def abRow : List (Prog isa) := [
  .block (rowStart 5 ++ ([.mov .rcx (.mem (wm oU)), .mov .rbp (.mem (wm oV))] : List Instr) ++
    ones oU oMu oV oMv .r10 ++ ([.mov32 .r11 (.imm 0), .mov32 .r12 (.imm 0)] : List Instr) ++
    term3 (px 0) (.reg .rcx) oMu .r10 .r11 .r12 ++ term3 (py 0) (.reg .rbp) oMv .r10 .r11 .r12 ++
    kOf oKd .r10 .r11 .r12 ++ shift3 .r10 .r11 .r12 ++
    ones oQ oMq oR oMr .r13 ++ ([.mov32 .r14 (.imm 0), .mov32 .rbx (.imm 0)] : List Instr) ++
    term3 (px 0) (.slot oQ) oMq .r13 .r14 .rbx ++ term3 (py 0) (.slot oR) oMr .r13 .r14 .rbx ++
    kOf oKe .r13 .r14 .rbx ++ shift3 .r13 .r14 .rbx ++ ([.alu .add .r8 (.imm 8)] : List Instr)),
  .loop (.block (abCol ++ ([.store (px (-8)) .r10, .store (py (-8)) .r13] : List Instr) ++
    shift3 .r10 .r11 .r12 ++ shift3 .r13 .r14 .rbx ++ next)) .ne,
  .block (signX (px (-8)) ++ termR oU oMu .r10 .r11 .r12 ++ signX (px (-8)) ++ termR oQ oMq .r13 .r14 .rbx ++
    signX (py (-8)) ++ termR oV oMv .r10 .r11 .r12 ++ signX (py (-8)) ++ termR oR oMr .r13 .r14 .rbx ++
    ([.store (px (-8)) .r10, .store (py (-8)) .r13] : List Instr) ++ rowEnd 5)]

/-- A batch: the divsteps, the coefficients' magnitudes and signs, `(f, g)` and `(a, b)` a row
each, and the count less one. -/
def batch : Prog isa := seqs ([.block (bStart ++ bWords ++ bSave ++ absS oU oMu ++ absS oV oMv ++ absS oQ oMq ++
  absS oR oMr)] ++ fgRow ++ abRow ++ [.block [.alu .sub .rsi (.imm 1)]])

/-- A batch of the GCD alone: `batch` without `(a, b)`. -/
def batchG : Prog isa := seqs ([.block (bStart ++ bWords ++ bSave ++ absS oU oMu ++ absS oV oMv ++ absS oQ oMq ++
  absS oR oMr)] ++ fgRow ++ [.block [.alu .sub .rsi (.imm 1)]])

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

/-- `rbp` the mask of `[j] < 0` (its word `n`'s top bit set). -/
def isNeg (j : Nat) : List Instr :=
  base j .rbx ++ ([.mov .rax (.mem (ix .rbx .r13)), .shift .shr .rax 63, .mov32 .rbp (.imm 0),
    .alu .sub .rbp (.reg .rax)] : List Instr)

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
`t = ±a 2^(5 B) mod m`; `|f|` into the cleared `aA` (`f` if `f ≥ 0`, then
`-f` if `f < 0`), so its words above `n` are zero; then `[v] = |f|` and
`[x₂] = t`. -/
def finish (iV iX₂ : Nat) : List (Prog isa) := [
  .block unwin, zeroI aT,
  .block (countN ++ base aA .r8 ++ ([.mov .rax (.mem (ix .r8 .r13)), .shift .shr .rax 63, .mov32 .r15 (.imm 0),
    .alu .sub .r15 (.reg .rax), .mov32 .rbp (.imm 0)] : List Instr) ++ base aT .rbx ++ base aP .r10),
  wordLoop 0 addMBody] ++ csubT ++ [
  .block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aP .r8 ++ base aT .r10 ++ base aS .rsi), wordLoop 0 subBody,
  .block (nonNeg aF ++ base aT .r8 ++ base aS .rsi), wordLoop 0 selBody,
  .block [.mov .r11 (.reg .r13), .shift .shl .r11 4, .alu .sub .r11 (.reg .r13), .alu .add .r11 (.imm 10)],
  .loop dbl .ne] ++ csubT ++ [
  zeroI aA,
  .block (countN ++ ([.mov32 .rbp (.imm 0)] : List Instr) ++ base aA .r8 ++ base aF .r10 ++ base aS .rsi),
  wordLoop 0 subBody,
  .block (isNeg aF ++ base aA .r8 ++ base aF .rsi), wordLoop 0 selBody,
  .block (nonNeg aF ++ base aA .r8 ++ base aS .rsi), wordLoop 0 selBody,
  copyI iV aA, copyI iX₂ aT]

/-- `finish` without the doublings: `t := a mod m`, `t := m - t` if `f < 0`
and a last subtraction (so `t < m`, `t ≡ ±a`), `[v] = |f|` and `[x₂] = t`,
for a caller that scales `t` by `2^(5 B)` itself. -/
def finishS (iV iX₂ : Nat) : List (Prog isa) := [
  .block unwin, zeroI aT,
  .block (countN ++ base aA .r8 ++ ([.mov .rax (.mem (ix .r8 .r13)), .shift .shr .rax 63, .mov32 .r15 (.imm 0),
    .alu .sub .r15 (.reg .rax), .mov32 .rbp (.imm 0)] : List Instr) ++ base aT .rbx ++ base aP .r10),
  wordLoop 0 addMBody] ++ csubT ++ [
  .block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aP .r8 ++ base aT .r10 ++ base aS .rsi), wordLoop 0 subBody,
  .block (nonNeg aF ++ base aT .r8 ++ base aS .rsi), wordLoop 0 selBody] ++ csubT ++ [
  zeroI aA,
  .block (countN ++ ([.mov32 .rbp (.imm 0)] : List Instr) ++ base aA .r8 ++ base aF .r10 ++ base aS .rsi),
  wordLoop 0 subBody,
  .block (isNeg aF ++ base aA .r8 ++ base aF .rsi), wordLoop 0 selBody,
  .block (nonNeg aF ++ base aA .r8 ++ base aS .rsi), wordLoop 0 selBody,
  copyI iV aA, copyI iX₂ aT]

/-- The end of the GCD alone: `[v] = |f|`. -/
def finishG (iV : Nat) : List (Prog isa) := [
  .block unwin, zeroI aA,
  .block (countN ++ ([.mov32 .rbp (.imm 0)] : List Instr) ++ base aA .r8 ++ base aF .r10 ++ base aS .rsi),
  wordLoop 0 subBody,
  .block (isNeg aF ++ base aA .r8 ++ base aF .rsi), wordLoop 0 selBody,
  .block (nonNeg aF ++ base aA .r8 ++ base aS .rsi), wordLoop 0 selBody,
  copyI iV aA]

end Inv

/-- The inverse at the width `n` in `r13`. -/
def inverseN (iU iV iX₂ iM : Nat) : Prog isa :=
  seqs (Inv.start iU iM ++ [.loop Inv.batch .ne] ++ Inv.finish iV iX₂)

/-- `inverseN` without the final doublings (`Inv.finishS`): `[x₂] ≤ m` with
`[x₂] 2^(5 B) a ≡ [v] (mod m)`, `B = 3 n + 2`. -/
def inverseNS (iU iV iX₂ iM : Nat) : Prog isa :=
  seqs (Inv.start iU iM ++ [.loop Inv.batch .ne] ++ Inv.finishS iV iX₂)

/-- The inverse at the width `w`. -/
def inverse (iU iV iX₂ iM : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.mov .r13 (.reg .r12)] : List Instr))) (inverseN iU iV iX₂ iM)

/-- The inverse at the width that `k` puts into `r13` after `ws`. -/
def inverseK (k : List Instr) (iU iV iX₂ iM : Nat) : Prog isa :=
  .seq (.block (ws ++ k)) (inverseN iU iV iX₂ iM)

/-- `[v] = gcd(u, m)` alone, at the width `n` in `r13`: the inverse's batches without `(a, b)`
(`Inv.batchG`), and no `[x₂]`. -/
def gcdN (iU iV iM : Nat) : Prog isa :=
  seqs (Inv.start iU iM ++ [.loop Inv.batchG .ne] ++ Inv.finishG iV)

/-- `gcdN` at the width `w`. -/
def gcdW (iU iV iM : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.mov .r13 (.reg .r12)] : List Instr))) (gcdN iU iV iM)

/-- `r13 := w / 2`. -/
def kHalf : List Instr := [.mov .r13 (.reg .r12), .shift .shr .r13 1]

/-- `r13 := 1`. -/
def kOne : List Instr := [.mov32 .r13 (.imm 1)]

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

end VG.Impl.Rsa.X86_64.Keys

namespace VG.Impl.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

def aR : Nat := 3
def aD : Nat := 5
def aT : Nat := 8
def aM : Nat := 9
def aV : Nat := 16

def wm (d : Nat) : MemOp := { base := .rbp, disp := d }

/-- Invalid factors still enter a normalized, fixed-width computation. -/
def normalize : List Instr :=
  ws ++ base aM .r10 ++
  [.shift .shr .r12 1, .mov .rax (.mem (ix .r10 .r12 (-8))),
    .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax]

def recipSetup : List Instr :=
  ws ++ base aM .r10 ++ base aV .r8 ++ [.shift .shr .r12 1]

def countSetup : List Instr :=
  ws ++ base aV .rbp ++ [.mov .rax (.reg .r12), .store (wm 16) .rax]

def stepLoad : List Instr :=
  ws ++ base aV .rbp ++ base aD .r11 ++ [.mov .rcx (.mem (wm 16))]

def stepDigit : List Instr :=
  ([.alu .sub .rcx (.imm 1), .mov .rdx (.mem (ix .r11 .rcx)),
    .store (wm 8) .rdx] : List Instr) ++
  base aR .rbx ++ base aM .r10 ++ base aT .r8 ++ [.shift .shr .r12 1]

def stepSetup : List Instr := stepLoad ++ stepDigit

def next : List Instr :=
  ws ++ base aV .rbp ++ [.mov .rax (.mem (wm 16)), .alu .sub .rax (.imm 1), .store (wm 16) .rax]

def body : Prog isa := seqs [.block stepSetup, WordReduce.step, .block next]

def code : Prog isa := seqs [
  zeroA aR, .block recipSetup, R2Words.recip, .block countSetup, .loop body .ne]

end VG.Impl.Rsa.X86_64.WordDivide


namespace VG.Impl.Rsa.X86_64.Keys

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

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

/-- The factors' bases and widths for `mulRows`, `⌈p_len / 8⌉` rows of `⌈q_len / 8⌉`
words, and the product's base. The product occupies arrays 2 and 3, leaving the factors
and `d` alone. -/
def productSetup : List Instr :=
  ws ++ base aP .r11 ++ base aQ .rax ++ base aU .r8 ++
    ([.mov .r9 (.reg .rax), .mov .r10 (.mem (hdr sPl)), .alu .add .r10 (.imm 7), .shift .shr .r10 3,
      .mov .r12 (.mem (hdr sQl)), .alu .add .r12 (.imm 7), .shift .shr .r12 3] : List Instr)

/-- The mask of `p q = n` and'ed into `sMask`, comparing all `2 w + 2`
words of the product so an overflowing product cannot pass. -/
def pqCheck : List (Prog isa) :=
  Crt.zeroAccs ++ [.block productSetup, Crt.mulRows] ++ Crt.eqCheck

/-- `r13 := ⌈max(p_len, q_len) / 8⌉`, the primes' width in words, without a
branch (`cmovb`). -/
def nPQ : List Instr :=
  [.mov .r13 (.mem (hdr sPl)), .mov .rax (.mem (hdr sQl)), .alu .cmp .r13 (.reg .rax), .cmov .b .r13 (.reg .rax),
    .alu .add .r13 (.imm 7), .shift .shr .r13 3]

/-- `[aC] := [j] - 1` (for an odd `[j]`, whose low word is not zero), then `[aU] := d`. -/
def divisor (j : Nat) : List (Prog isa) :=
  [zeroA aC, copyA aC j, .block (decA aC), zeroA aU, copyA aU aD]

/-- Public pointer setup for the common balanced-key layout. -/
def wordGuardHead : List Instr := ws ++ [.mov .rdx (.mem (hdr sN))]

/-- Zero exactly for full-word balanced factors and a full-size modulus. -/
def wordGuardTail : List Instr :=
  [.mov .rax (.reg .r12), .alu .and .rax (.imm 1),
    .mov .rcx (.reg .r12), .shift .shl .rcx 3, .alu .xor .rcx (.mem (hdr sK)), .alu .or .rax (.reg .rcx),
    .mov .rcx (.mem (hdr sPl)), .shift .shl .rcx 1, .alu .xor .rcx (.mem (hdr sK)), .alu .or .rax (.reg .rcx),
    .mov .rcx (.mem (hdr sPl)), .alu .xor .rcx (.mem (hdr sQl)), .alu .or .rax (.reg .rcx),
    .movzx8 .rcx { base := .rdx }, .shift .shr .rcx 7, .alu .xor .rcx (.imm 1), .alu .or .rax (.reg .rcx)]

/-- Word reductions are selected using public lengths and the modulus. -/
def wordChoice (j : Nat) : Prog isa := .seq (.block wordGuardHead) (.seq (.block wordGuardTail)
  (.ite .e (.seq (seqs (divisor j)) (.seq (.block WordDivide.normalize) WordDivide.code))
    (seqs (divisor j ++ [divmod aU aV aC aT]))))

/-- `a` where the public guard of `wordChoice` holds, else `b`. -/
def guarded (a b : Prog isa) : Prog isa := .seq (.block wordGuardHead) (.seq (.block wordGuardTail) (.ite .e a b))

/-- The array that keeps `d` while `qTail` uses `WordDivide`'s dividend. -/
def aSv : Nat := 10

/-- `r13 := n = w / 2` and `rax := K - 1` for the inverse's `K = 5 B = 15 n + 10`,
from `w` in `r12`. -/
def tailK : List Instr :=
  [.mov .r13 (.reg .r12), .shift .shr .r13 1, .mov .rax (.reg .r13), .shift .shl .rax 4,
    .alu .sub .rax (.reg .r13), .alu .add .rax (.imm 9)]

/-- `r11 := (K - 1) mod 64 + 1`, the doublings (`1` to `64`), and `r12 := n + 1`. -/
def dblSetup : List Instr :=
  ws ++ tailK ++ [.mov .r11 (.reg .rax), .alu .and .r11 (.imm 63), .alu .add .r11 (.imm 1),
    .mov .r12 (.reg .r13), .alu .add .r12 (.imm 1)]

/-- `[x₂] := 2 [x₂]` over its low `r12 = n + 1` words, and `r11` less one. -/
def tailDbl : Prog isa :=
  seqs [.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aX₂ .rbx), wordLoop 0 shlBody,
    .block [.alu .sub .r11 (.imm 1)]]

/-- `r13 := ⌊(K - 1) / 64⌋`, `r12 := w - r13`, `rsi` at `[x₂]` and `rbx` at
word `r13` of `[d]`: `copyWords` then puts `[x₂] 2^(64 r13)` into `[d]`. -/
def place : List Instr :=
  ws ++ tailK ++ [.shift .shr .rax 6, .mov .r13 (.reg .rax), .alu .sub .r12 (.reg .r13), .shift .shl .r13 3] ++
    base aX₂ .rsi ++ base aD .rbx ++ [.alu .add .rbx (.reg .r13)]

/-- On the guarded path, `[x₂] := [x₂] 2^K mod p` for the inverse's
`K = 5 B = 15 n + 10`: `[x₂]` doubled `(K - 1) mod 64 + 1` times, placed
`⌊(K - 1) / 64⌋` words up in `WordDivide`'s dividend `[d]` (kept in
`[aSv]`), and reduced by `WordDivide` modulo `p` (normalized). -/
def qTail : List (Prog isa) := [
  zeroA aSv, copyA aSv aD,
  .seq (.block dblSetup) (.loop tailDbl .ne),
  zeroA aD, .seq (.block place) copyWords,
  zeroA aC, copyA aC aP, .seq (.block WordDivide.normalize) WordDivide.code,
  zeroA aX₂, copyA aX₂ aV, copyA aD aSv]

/-- The mask of `gcd(q, p) = 1`, from the inverse's `[v]`, and'ed into the mask. -/
def gcdPart : List (Prog isa) := [zeroA aC, .block (setOneA aC)] ++ (eqA aV aC ++ [.block andZero])

/-- `qInv = q⁻¹ mod p` by the inverse at the primes' width, and the mask of
`gcd(q, p) = 1`: where the public guard holds, by `inverseNS` and `qTail`
(the inverse's `2^K` by `WordDivide`), else by `inverseN`. -/
def invPart : List (Prog isa) :=
  [guarded (.seq (.block (ws ++ nPQ)) (inverseNS aQ aV aX₂ aP)) (.seq (.block (ws ++ nPQ)) (inverseN aQ aV aX₂ aP))] ++
    gcdPart ++ [guarded (seqs qTail) (.block [])]

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([
  .block head] ++ loadA aN sN sK ++ loadA aP sP sPl ++ loadA aQ sQ sQl ++ loadA aD sD sDl ++ pqCheck ++ invPart ++
  -- `dP = d mod (p - 1)` into `aX₁` and `dQ = d mod (q - 1)` in `aV`.
  [wordChoice aP, zeroA aX₁, copyA aX₁ aV, wordChoice aQ] ++
  storeA aX₂ sQi sPl sMask ++ storeA aX₁ sDp sPl sMask ++ storeA aV sDq sQl sMask ++
  [.block retMask])

/-- `vg_rsa_crt_values`. -/
def code : Prog isa :=
  .seq (.block (entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid)) (.ite .ne fail main)

end CrtValues

end VG.Impl.Rsa.X86_64.Keys
