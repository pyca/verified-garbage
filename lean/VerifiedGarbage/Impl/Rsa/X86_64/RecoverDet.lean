module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-!
# `vg_rsa_recover_primes_det` on x86-64

SP 800-56B Rev. 2 Appendix C.2 without a branch on a secret, in the working
space of `Keys.lean` at two widths, which the header gives (`width`):
narrow numbers of `v = h + 1` words (`h = ⌈k / 8⌉`, the modulus's words),
and wide numbers of `W = 2 v + 2` words, wide array `j` being narrow arrays
`2 j` and `2 j + 1`. A wide loop in the narrow layout doubles `r12` after
`ws` (`wideR`). Every loop's count and every branch depends only on `k`.

1. `d e` (`Recover.prod`), then `x = d e - 1` and whether `d e ≥ 2`
   (`deMinus`).
2. The twos (`twos`, narrow). With `u = n - 1` (not zero, below `2^(64 h)`)
   and `x₂ = x`: `t = min(tz u, tz x₂) = tz (u ∨ x₂) < 64 h`; `u := u / 2^(tz u)`,
   `x₂ := x₂ / 2^t`, `x := x 2^t`. Each of the two counts is taken by
   stages from the largest down (`stageW`, `stageB`): stages of `c` words
   for `c = 64, 32, …, 1` where `c ≤ v - 2` (a branch on `k`), then of `b`
   bits for `b = 32, …, 1`. A stage tests whether the low `s` bits
   (`s = 64 c` or `b`) of `u ∨ x₂` (or of `u`) are zero, and if so shifts
   by `s`: after the larger stages the count left is below `2 s`, so the
   stages taken are exactly its bits (`Proof/Bignum/ShiftStages.lean`).
   Each shift is computed into a temporary and selected under the stage's
   mask (`selBody`).
3. `g = gcd(u, x₂)` by the batched GCD alone (`Keys.gcdW`).
4. `a = g x` (wide, `a < 2^(64 (2 h + 1))`), `m = ⌊a / n⌋`, `r = a mod n`
   and whether `m < n` (`divA`): by word steps (`qDiv`) once `n` and `a`
   are shifted left by `z`, the leading zeros of `n`'s top word (public,
   below 64, as that word is not zero), and the remainder back by `z`.
5. `D = m + 1` and `N = n - r`, `b - 1 = N / D`, and whether `N mod D = 0`
   (`divB`, wide). Where `m < n` (else the mask is already clear), `D`
   has at most `h` words; its leading zeros `s = 64 c + z` in `h` words are
   found without a branch (`clzOf`: a scan for the top nonzero word, then
   six stages within it), `D` and `N` are shifted by `s` (stages of `2^j`
   words for the bits `j` of `c`, under masks, then a shift by `z` in `cl`),
   and `qDiv` divides: the quotient is `N / D`, the remainder
   `(N mod D) 2^s`, zero exactly when `N mod D` is. `D`'s top bit is set
   regardless, so that the steps' precondition holds when the mask is clear.
6. `b² - 4 n` (rows of `v` words), and whether `b² > 4 n` (`minus4n`).
7. Its integer square root (`sqrt`, narrow), two bits at a time from the
   top: `b ≤ n + 1 ≤ 2^(64 h)`, so `X = b² - 4 n < 2^(128 h)` takes
   `64 h` steps. Step `p` (from `64 h - 1` down) reads bits `2 p + 1` and
   `2 p` of `X` (word `p / 32`, shifted by `2 p mod 64`), then:
   `rem := 4 rem + pair`; `t := rem - (4 y + 1)`; `rem := t` and
   `y := 2 y + 1` if it does not borrow, else `y := 2 y`. Before step `p`
   the root has `i = 64 h - 1 - p` bits and the remainder at most `i + 1`,
   so the step runs over `L = ⌊i / 64⌋ + 2 ≤ v` words (`lenS`).
8. `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
   check (`sMask`).

`qDiv e` divides a wide dividend of `2 h + e - 1` words by a normalized
divisor of `h` words, as `vg_rsa_crt_values`'s `WordDivide` does: the
remainder starts as the dividend's top `h - 1` words, then `h + e` steps
(`WordReduce.step`, the 3-by-2 estimate `q̂` and one masked correction)
bring down its other words from the top; each step's quotient digit is
`q̂` plus the correction's mask (`-1` or `0`), stored at the digit's index.

The arguments' header slots, the entry, the failure path and the product
`d e` are in the namespace `Recover`.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.Keys.Recover

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Keys

/-! ## The layout -/

/-- Header slots: `p` and `q`'s pointers, and `d`'s pointer and length (`n`
and `e` in `vg_rsa_public`'s `sN`, `sK`, `sE` and `sElen`). -/
def sP : Nat := sOut
def sQ : Nat := sIn
def sD : Nat := sI
def sDl : Nat := sBit
/-- Arrays, after `vg_rsa_public`'s 0 to 7: `e` (8), `d` (9), and `M = d e`
over 10 and 11. -/
def aE : Nat := 8
def aD : Nat := 9
def aM : Nat := 10
/-- The stack argument `i` (from 1). -/
def stk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-! ## The entry and the exits -/

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`. `p_len` and `q_len` are `n_len`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem (stk 5))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  ([.store { base := .r11, disp := 8 * sP } .rdi, .store { base := .r11, disp := 8 * sQ } .rdx,
    .store { base := .r11, disp := 8 * sN } .r8, .store { base := .r11, disp := 8 * sK } .r9,
    .mov .rax (.mem (stk 1)), .store { base := .r11, disp := 8 * sE } .rax,
    .mov .rax (.mem (stk 2)), .store { base := .r11, disp := 8 * sElen } .rax,
    .mov .rax (.mem (stk 3)), .store { base := .r11, disp := 8 * sD } .rax,
    .mov .rax (.mem (stk 4)), .store { base := .r11, disp := 8 * sDl } .rax, .mov .rdi (.reg .r11)] : List Instr)

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut sP sK, zeroOut sQ sK, .block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)]

/-! ## `d e` -/

/-- The bases of `e`, `M` and `d` into `rbx`, `r10` and `r15`, the words of
`e` into `r11`, and the row counter `r13 := 0`. -/
def prodInit : List Instr :=
  ws ++ base aE .rbx ++ base aM .r10 ++ base aD .r15 ++
    ([.mov .r11 (.mem (hdr sElen)), .alu .add .r11 (.imm 7), .shift .shr .r11 3, .mov32 .r13 (.imm 0)] : List Instr)

/-- Row `r13`: `rcx := e[r13]`, the accumulator at word `r13` of `M`, and
`d`'s base in `r9`. -/
def rowHead : List Instr :=
  [.mov .rcx (.mem (ix .rbx .r13)), .mov .r8 (.reg .r13), .alu .add .r8 (.reg .r8), .alu .add .r8 (.reg .r8),
    .alu .add .r8 (.reg .r8), .alu .add .r8 (.reg .r10), .mov .r9 (.reg .r15)]

/-- The row counter against `r11`. -/
def rowNext : List Instr := [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r11)]

/-- `M := d e`: `M += e_j d` at word `j`, for each word `j` of `e`. -/
def prod : List (Prog isa) :=
  [zeroA aM, zeroA (aM + 1),
    .seq (.block prodInit) (.loop (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) .ne)]

end VG.Impl.Rsa.X86_64.Keys.Recover

namespace VG.Impl.Rsa.X86_64.Keys.RecoverDet

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover (sP sQ sD sDl aE aD aM prod)

/-! ## Header slots -/

/-- A loop's count, `clzOf`'s word count `c`, a stage's mask `keep`, and
`clzOf`'s bit count `z` or a borrow of the square root. -/
def sCt : Nat := sFn 9
def sU : Nat := sFn 10
def sB2 : Nat := sFn 11
def sC : Nat := sFn 14

/-! ## Widths -/

/-- The narrow width `v = ⌈k / 8⌉ + 1`, or the wide `2 v + 2`, into `r12`,
the header's `w`, the arrays' bases and the stride. -/
def width (wide : Bool) : List Instr :=
  ([.mov .r12 (.mem (hdr sK)), .alu .add .r12 (.imm 7), .shift .shr .r12 3, .alu .add .r12 (.imm 1)] : List Instr) ++
  (if wide then ([.alu .add .r12 (.reg .r12), .alu .add .r12 (.imm 2)] : List Instr) else []) ++
  ([.store (hdr sW) .r12] : List Instr) ++ setBases ++
  ([.mov .rax (.reg .r12), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .store (hdr sStride) .rax] : List Instr)

/-- The narrow width, and the mask all ones. -/
def head : List Instr := width false ++ ([.mov .rax (.imm (BitVec.ofInt 32 (-1))), .store (hdr sMask) .rax] : List Instr)

/-- `r12 := 2 r12 + 2`: the wide width, from the narrow one. -/
def wideR : List Instr := [.alu .add .r12 (.reg .r12), .alu .add .r12 (.imm 2)]

/-! ## Pieces over arrays by their index -/

/-- `[t] := [a] - [b]`, `rbp` the mask of its borrow. -/
def subA (t a b : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.mov32 .rbp (.imm 0)] : List Instr) ++ base a .r8 ++ base b .r10 ++ base t .rsi))
    (wordLoop 0 subBody)

/-- `[o] := [a] + [b]`, modulo `2^(64 w)`. -/
def addA (o a b : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rbp (.imm 0)] : List Instr) ++
    base b .r10 ++ base a .r8 ++ base o .rbx)) (wordLoop 0 addMBody)

/-- `[j] := [j] / 2` (its word `w` zero). -/
def shrA (j : Nat) : Prog isa := .seq (.block (ws ++ base j .r8 ++ base j .rsi)) (wordLoop 0 shrBody)

/-- `[j] := 2 [j] + c` modulo `2^(64 w)`, for the carry in `rbp` that `pre` leaves, `w`
doubled first if `wide`. -/
def shlA (wide : Bool) (j : Nat) (pre : List Instr) : Prog isa :=
  .seq (.block (ws ++ (if wide then wideR else []) ++ base j .rbx ++ pre)) (wordLoop 0 shlBody)

/-- The mask of `rbp` (all ones or zero) and'ed into `sMask`. -/
def andNz : List Instr := [.alu .and .rbp (.mem (hdr sMask)), .store (hdr sMask) .rbp]

/-- The count less one, and `ZF` if it is zero. -/
def countNext : List Instr := [.mov .rax (.mem (hdr sCt)), .alu .sub .rax (.imm 1), .store (hdr sCt) .rax]

/-! ## `d e - 1` (wide) -/

def deMinus : List (Prog isa) := [zeroA 1, .block (setOneA 1),
  subA 2 5 1, .block CrtValues.andZero, subA 3 2 1, .block CrtValues.andZero]

/-! ## Shifts by stages -/

/-- `r12 := h = W / 2 - 2` from the wide width `W`. -/
def hOf : List Instr := [.shift .shr .r12 1, .alu .sub .r12 (.imm 2)]

/-! ### Shifts through a temporary

Over the header's `w` words, or the wide `2 w + 2` at the narrow width if
`wd` (`wsW`). A shift by whole words copies the words that remain into a
cleared temporary at their new places; a shift by `cl < 64` bits combines
each word with its neighbour's (`shrClBody`, `shlClBody`); a masked shift
then selects the temporary's words where the stage's mask `keep` (`sB2`) is
clear (`selK`). -/

/-- `ws`, then the wide width if `wd`. -/
def wsW (wd : Bool) : List Instr := ws ++ (if wd then wideR else [])

/-- `[j] := keep ? [j] : [t]`. -/
def selK (wd : Bool) (j t : Nat) : Prog isa :=
  .seq (.block (wsW wd ++ base j .r8 ++ base t .rsi ++ ([.mov .rbp (.mem (hdr sB2))] : List Instr)))
    (wordLoop 0 selBody)

/-- `[t] := [j] / 2^(64 c)` (`[t]` cleared). -/
def shrWords (j c t : Nat) : List (Prog isa) :=
  [zeroA t,
   .seq (.block (ws ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
      ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx)) copyWords]

/-- `[t] := [j] 2^(64 c)` modulo `2^(64 n)` (`[t]` cleared, two arrays if `wd`). -/
def shlWords (wd : Bool) (j c t : Nat) : List (Prog isa) :=
  [zeroA t] ++ (if wd then [zeroA (t + 1)] else []) ++
  [.seq (.block (wsW wd ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
      base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))) copyWords]

/-- Word `i` of `[r8] / 2^cl` into `[rsi]` (`cl < 64`): its word `i` shifted right and
word `i + 1` left by `64 - cl`, as `(x / 2) / 2^(63 - cl)`. -/
def shrClBody : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14)), .shiftCl .shr .rax, .mov .rdx (.mem (ix .r8 .r14 8)), .shift .shl .rdx 1,
    .alu .xor .rcx (.imm 63), .shiftCl .shl .rdx, .alu .xor .rcx (.imm 63), .alu .add .rax (.reg .rdx),
    .store (ix .rsi .r14) .rax]

/-- `[t] := [j] / 2^cl`, for `cl` that `pre` leaves in `rcx` (word `n` of `[j]` zero). -/
def shrCl (wd : Bool) (j t : Nat) (pre : List Instr) : Prog isa :=
  .seq (.block (wsW wd ++ base j .r8 ++ base t .rsi ++ pre)) (wordLoop 0 shrClBody)

/-- `[t] := [j] 2^cl` modulo `2^(64 n)`, for `cl` that `pre` leaves in `rcx`. -/
def shlCl (wd : Bool) (j t : Nat) (pre : List Instr) : Prog isa :=
  .seq (.block (wsW wd ++ base j .r8 ++ base t .rsi ++ pre ++
    ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] : List Instr))) (wordLoop 1 shlClBody)

/-- `rcx := b`. -/
def clOf (b : Nat) : List Instr := [.mov32 .rcx (.imm (BitVec.ofNat 32 b))]

/-! ### The stages' tests -/

/-- `rbp := ` the mask `keep` from `rbp` (zero: shift), into `sB2`. -/
def keepOf : List Instr :=
  [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1))),
    .store (hdr sB2) .rbp]

/-- Word `i` of `[rbx]` or'ed into `rbp`. -/
def or1Body : List Instr := [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)]

/-- Words `i` of `[rbx]` and `[r10]` or'ed into `rbp`. -/
def or2Body : List Instr :=
  [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)]

/-- `keep` of the low `c` words of `u`, and of `x₂` if `both`, not all zero. -/
def testW (both : Bool) (c : Nat) : List (Prog isa) :=
  [.seq (.block (ws ++ base 7 .rbx ++ base 6 .r10 ++
      ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))
    (wordLoop 0 (if both then or2Body else or1Body)),
   .block keepOf]

/-- `keep` of the low `b` bits of `u`'s low word, or'ed with `x₂`'s if `both`, not all zero. -/
def testB (both : Bool) (b : Nat) : List (Prog isa) :=
  [.block (ws ++ base 7 .rbx ++ base 6 .r10 ++ ([.mov .rax (.mem (at0 .rbx))] : List Instr) ++
    (if both then [.alu .or .rax (.mem (at0 .r10))] else []) ++
    ([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr) ++ keepOf)]

/-- `keep` of the top `c` of the low `h` words of `[j]` not all zero (wide). -/
def testTop (j c : Nat) : List (Prog isa) :=
  [.seq (.block (ws ++ base j .rbx ++ hOf ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3,
      .alu .add .rbx (.reg .r12), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))
    (wordLoop 0 or1Body),
   .block keepOf]

/-! ## The twos (narrow)

`u` (7), `x₂` (6) and `x` (wide 2, narrow 4); the temporaries narrow 14, or
wide 7. -/

/-- `x₂` and `u = n - 1`, cleared above their words; `g`'s arrays cleared. -/
def twosInit : List (Prog isa) := [zeroA 6, copyA 6 4, zeroA 7, subA 7 0 2, zeroA 12, zeroA 13]

/-- A stage of `c` words, where `c ≤ v - 2`. -/
def stageW (both : Bool) (c : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 2)))] : List Instr)))
    (.ite .b (.block []) (seqs (testW both c ++ shrWords 7 c 14 ++ [selK false 7 14] ++
      (if both then shrWords 6 c 14 ++ [selK false 6 14] ++ shlWords true 4 c 14 ++ [selK true 4 14] else []))))

/-- A stage of `b` bits. -/
def stageB (both : Bool) (b : Nat) : List (Prog isa) :=
  testB both b ++ [shrCl false 7 14 (clOf b), selK false 7 14] ++
  (if both then [shrCl false 6 14 (clOf b), selK false 6 14, shlCl true 4 14 (clOf b), selK true 4 14] else [])

/-- The stages' sizes: words, then bits. -/
def wordStages : List Nat := [64, 32, 16, 8, 4, 2, 1]
def bitStages : List Nat := [32, 16, 8, 4, 2, 1]

/-- `u ∨ x₂`'s twos off `u` and `x₂` and onto `x`, then `u`'s own. -/
def twos : List (Prog isa) :=
  wordStages.map (stageW true) ++ (bitStages.map (stageB true)).flatten ++
  wordStages.map (stageW false) ++ (bitStages.map (stageB false)).flatten

/-! ## Division by words (wide) -/

/-- `rdx`'s leading zeros added to `r11` by a stage of `b` bits, `rdx` shifted by them. -/
def clzStage (b : Nat) : List Instr :=
  [.mov .rcx (.reg .rdx), .shift .shr .rcx (64 - b), .mov .r8 (.reg .rdx), .shift .shl .r8 b,
    .alu .cmp .rcx (.imm 1), .cmov .b .rdx (.reg .r8), .alu .sbb .r9 (.reg .r9), .alu .and .r9 (.imm (BitVec.ofNat 32 b)),
    .alu .add .r11 (.reg .r9)]

/-- `sC := z`, the leading zeros of word `h - 1` of `[j]` (below 64 where it is not zero). -/
def clzTop (j : Nat) : List Instr :=
  ws ++ base j .rbx ++ hOf ++ ([.mov .rdx (.mem (ix .rbx .r12 (-8))), .mov32 .r11 (.imm 0)] : List Instr) ++
  ([32, 16, 8, 4, 2, 1].map clzStage).flatten ++ ([.store (hdr sC) .r11] : List Instr)

/-- `[d] := [a] 2^z` (`z = sC`). -/
def shlZ (a d : Nat) : Prog isa := shlCl false a d [.mov .rcx (.mem (hdr sC))]

/-- `[d] := [a] / 2^z` (`z = sC`). -/
def shrZ (a d : Nat) : Prog isa := shrCl false a d [.mov .rcx (.mem (hdr sC))]

/-! ### The division

`qDiv e`'s arrays (wide): the dividend 9, the quotient 11, the remainder 12,
the divisor 8, the working space 13 and the window 14. -/

def qA : Nat := 9
def qQ : Nat := 11
def qR : Nat := 12
def qD : Nat := 8
def qT : Nat := 13
def qV : Nat := 14

/-- The remainder: the dividend's `h - 1` words from word `h + e`. -/
def qSeed (e : Nat) : Prog isa :=
  .seq (.block (ws ++ base qA .rsi ++ base qR .rbx ++ hOf ++
    ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
      .alu .sub .r12 (.imm 1)] : List Instr))) copyWords

/-- The window's and the dividend's bases, and the count `j + 1 = sCt`: public. -/
def qLoad : List Instr :=
  ws ++ base qV .rbp ++ base qA .r11 ++ ([.mov .rcx (.mem (hdr sCt))] : List Instr)

/-- The digit `[qA][j]` into the window; the step's other registers. -/
def qDigit : List Instr :=
  ([.alu .sub .rcx (.imm 1), .mov .rdx (.mem (ix .r11 .rcx)), .store { base := .rbp, disp := 8 } .rdx] : List Instr) ++
  base qR .rbx ++ base qD .r10 ++ base qT .r8 ++ hOf

/-- `rax := j + 1 = sCt` and the quotient's base: public. -/
def qPos : List Instr := ws ++ base qQ .rbx ++ ([.mov .rax (.mem (hdr sCt))] : List Instr)

/-- The digit `q̂ + mask` to word `j` of the quotient, and the count less one. -/
def qTail : List Instr :=
  [.alu .add .rcx (.reg .r11), .alu .sub .rax (.imm 1), .store (ix .rbx .rax) .rcx, .store (hdr sCt) .rax]

def qBody : Prog isa := seqs [.block (qLoad ++ qDigit), WordReduce.step, .block (qPos ++ qTail)]

/-- `[11] := [9] / [8]` and `[12] := [9] mod [8]` (wide), for the normalized
divisor `[8]` of `h` words and a dividend of `2 h + e - 1` words: `[12]`
starts as its top `h - 1` words, then `h + e` steps bring down its other words
from the top, each storing its quotient digit. -/
def qDiv (e : Nat) : List (Prog isa) := [zeroA qQ, zeroA qR, zeroA qT, zeroA qV, qSeed e,
  .seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip,
  .block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] : List Instr)),
  .loop qBody .ne]

/-! ## `a`, `m`, `r` and whether `m < n` (wide) -/

/-- `e`'s length `8 v = 4 W - 8`, for `Recover.prod`'s multiplier of `v` words. -/
def setEl : List Instr :=
  ws ++ ([.mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .sub .rax (.imm 8),
    .store (hdr sElen) .rax] : List Instr)

/-- `a = g x` (wide 10); `m = a / n` into wide 7, `r = a mod n` into wide 6 and
`m < n` into the mask: `n`'s top word is not zero, so `z = clz n < 64` normalizes
it, and `a 2^z < 2^(64 (2 h + 2))`. -/
def divA : List (Prog isa) := [.block setEl, copyA 8 6, copyA 9 2] ++ prod ++
  [.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9] ++ qDiv 3 ++
  [zeroA 6, shrZ 12 6, subA 14 11 0, .block andNz, copyA 7 11]

/-! ## `m + 1`, `n - r`, `b` (wide) -/

/-- A stage of `c` words of `D`'s leading zeros, where `c ≤ h - 1`: if the top `c`
of `D`'s `h` words are zero, `D` and `N` shifted left by `c` words. -/
def stageD (c : Nat) : Prog isa :=
  .seq (.block (ws ++ hOf ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 1)))] : List Instr)))
    (.ite .b (.block []) (seqs (testTop 2 c ++ shlWords false 2 c 3 ++ [selK false 2 3] ++
      shlWords false 5 c 3 ++ [selK false 5 3])))

/-- `D` (wide 2) and `N` (wide 5) times `2^s` into the divisor (8) and the dividend
(9), for `D`'s leading zeros `s` in `h` words: by word stages, then the top word's
leading zeros `z`; and the divisor's word `h - 1` with its top bit set. -/
def normDN : List (Prog isa) :=
  wordStages.map stageD ++ [.block (clzTop 2), zeroA 8, shlZ 2 8, zeroA 9, shlZ 5 9,
   .block (ws ++ base 8 .r10 ++ hOf ++ [.mov .rax (.mem (ix .r10 .r12 (-8))), .movImm64 .rdx 9223372036854775808,
    .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax])]

/-- `D = m + 1` (wide 2) and `N = n - r` (wide 5); `N / D` (wide 11) and whether its
remainder (wide 12) is zero; `b = N / D + 1` (wide 4). -/
def divB : List (Prog isa) :=
  [zeroA 5, subA 5 0 6, zeroA 2, addA 2 7 1] ++ normDN ++ qDiv 1 ++
  [zeroA 3] ++ eqA 12 3 ++ [.block CrtValues.andZero, zeroA 4, addA 4 11 1]

/-! ## `b² - 4 n` (wide) -/

/-- `M := b b`, rows of `v` words (`b < 2^(64 v)`). -/
def prodB : List (Prog isa) :=
  [zeroA aM, zeroA (aM + 1),
    .seq (.block (Recover.prodInit ++ ([.shift .shr .r12 1, .alu .sub .r12 (.imm 1)] : List Instr)))
      (.loop (.seq (.block Recover.rowHead) (.seq mulAddRow (.block Recover.rowNext))) .ne)]

def minus4n : List (Prog isa) := [copyA 8 4, copyA 9 4] ++ prodB ++
  [shlA false 0 [.mov32 .rbp (.imm 0)], shlA false 0 [.mov32 .rbp (.imm 0)],
    subA 12 10 0, .block CrtValues.andZero, subA 13 12 1, .block CrtValues.andZero, copyA 7 12]

/-! ## The square root (wide)

`X` (7, `2 h` words) normalized in place to `X' = X 4^c`, whose top word is at
least `2^62`; its root digit by digit, each a 3-by-2 estimate from the
remainder's top words and the root's (narrow scratch 5 and 1), then three
masked corrections. `D` (3) holds `2 s β + q̂` aligned to the step's word
`m = sCt - 1`, so that its top words stay in place; the remainder is `X'`'s
words from `2 m`. -/

def sqZ : Nat := 7
def sqT : Nat := 6
def sqD : Nat := 3
def sqU : Nat := 5
def sqS : Nat := 1
def sqR : Nat := 2
/-- Whether `X = 0` (a mask), and the word shift `K` of the normalization. -/
def sZ : Nat := sFn 13
def sK2 : Nat := sFn 15

/-- `keep` of the top `c` of `X`'s `2 h` words not all zero. -/
def testX (c : Nat) : List (Prog isa) :=
  [.seq (.block (ws ++ base sqZ .rbx ++ ([.mov .rax (.reg .r12), .alu .sub .rax (.imm (BitVec.ofNat 32 (c + 4))),
      .shift .shl .rax 3, .alu .add .rbx (.reg .rax), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))
    (wordLoop 0 or1Body),
   .block keepOf]

/-- `K := K + c` unless `keep`. -/
def addK (c : Nat) : List Instr :=
  [.mov .rax (.mem (hdr sB2)), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.imm (BitVec.ofNat 32 c)),
    .alu .add .rax (.mem (hdr sK2)), .store (hdr sK2) .rax]

/-- A stage of `c` words, where `c ≤ 2 h - 1`. -/
def stageX (c : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 5)))] : List Instr)))
    (.ite .b (.block []) (seqs (testX c ++ shlWords false sqZ c sqT ++ [selK false sqZ sqT, .block (addK c)])))

/-- `sC := ` the leading zeros of `X`'s word `2 h - 1`, made even. -/
def clzX : List Instr :=
  ws ++ base sqZ .rbx ++ ([.mov .rdx (.mem (ix .rbx .r12 (-40))), .mov32 .r11 (.imm 0)] : List Instr) ++
  ([32, 16, 8, 4, 2, 1].map clzStage).flatten ++
  ([.alu .and .r11 (.imm (BitVec.ofInt 32 (-2))), .store (hdr sC) .r11] : List Instr)

/-- `X`'s words `2 h` to `w - 1` cleared, so that `X < 2^(64 · 2 h)`. -/
def topX : List Instr :=
  ws ++ base sqZ .rbx ++ ([.mov32 .rax (.imm 0), .store (ix .rbx .r12 (-32)) .rax, .store (ix .rbx .r12 (-24)) .rax,
    .store (ix .rbx .r12 (-16)) .rax, .store (ix .rbx .r12 (-8)) .rax] : List Instr)

/-- `sZ := [X = 0]` (`rbp`, the words or'ed, on entry), `X := X + [X = 0]`, `K := 0`. -/
def zeroX : List Instr :=
  ws ++ base sqZ .rbx ++ ([.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .store (hdr sZ) .rbp,
    .mov .rax (.reg .rbp), .alu .and .rax (.imm 1), .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax,
    .mov32 .rax (.imm 0), .store (hdr sK2) .rax] : List Instr)

/-- `X := X mod 2^(64 · 2 h)`, then `1` if that is zero, then `X 4^c` for
`c = 32 K + z / 2`, its top word at least `2^62`. -/
def normX : List (Prog isa) :=
  [.block topX, .seq (.block (ws ++ base sqZ .rbx ++ ([.mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 or1Body),
   .block zeroX] ++
  (128 :: wordStages).map stageX ++ [.block clzX, shlZ sqZ sqT, copyA sqZ sqT]

/-- A step of the root of `(r11, r13) 4 + ` the top two bits of `(r8, r9)`:
`r10 := 2 r10 + 1` and the remainder less `4 r10 + 1` if that is not negative. -/
def isqBody : List Instr :=
  [.shld .r11 .r13 2, .shld .r13 .r8 2, .shld .r8 .r9 2, .shift .shl .r9 2,
   .mov .r14 (.reg .r10), .shift .shr .r14 62, .mov .r15 (.reg .r10), .shift .shl .r15 2, .alu .or .r15 (.imm 1),
   .mov .rax (.reg .r13), .alu .sub .rax (.reg .r15), .mov .rdx (.reg .r11), .alu .sbb .rdx (.reg .r14),
   .cmov .ae .r13 (.reg .rax), .cmov .ae .r11 (.reg .rdx), .alu .sbb .rbx (.reg .rbx),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.imm 1), .alu .add .r10 (.reg .rbx), .alu .sub .rcx (.imm 1)]

/-- The first digit `s₀` of `X'`'s top two words, its remainder in their place;
`D`'s words `h - 1` and `h` from `2 s₀`, `s₀` the scratch's word 2 and its
reciprocal word 0. -/
def firstX : List (Prog isa) :=
  [zeroA sqD, zeroA sqS, zeroA sqU,
   .seq (.block (ws ++ base sqZ .rbx ++ ([.mov .r8 (.mem (ix .rbx .r12 (-40))), .mov .r9 (.mem (ix .rbx .r12 (-48))),
      .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0), .mov32 .r13 (.imm 0), .mov32 .rcx (.imm 64)] : List Instr)))
    (.loop (.block isqBody) .ne),
   .block (ws ++ base sqZ .rbx ++ ([.store (ix .rbx .r12 (-40)) .r11, .store (ix .rbx .r12 (-48)) .r13] : List Instr) ++
     base sqD .rsi ++ hOf ++ ([.mov .rax (.reg .r10), .alu .add .rax (.reg .rax), .store (ix .rsi .r12 (-8)) .rax,
      .mov .rax (.reg .r10), .shift .shr .rax 63, .store (ix .rsi .r12) .rax] : List Instr) ++
     base sqS .rsi ++ ([.store { base := .rsi, disp := 16 } .r10] : List Instr)),
   .seq (.block (ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr))) R2Words.recip]

/-- The step's window: `rbx`, `r8 := X' + 16 m`, `r10 := D + 8 m`, `r12 := L = h - m + 2`. -/
def winPtrs : List Instr :=
  ws ++ base sqZ .rbx ++ base sqD .r10 ++ hOf ++
  ([.mov .rcx (.mem (hdr sCt)), .alu .sub .rcx (.imm 1), .alu .sub .r12 (.reg .rcx), .alu .add .r12 (.imm 2),
    .shift .shl .rcx 3, .alu .add .r10 (.reg .rcx), .alu .add .rbx (.reg .rcx), .alu .add .rbx (.reg .rcx),
    .mov .r8 (.reg .rbx)] : List Instr)

/-- `(x[a + 1], x[a]) / 2` modulo `2^64`, into scratch word `o` at `t`. -/
def half (x t : Reg) (a o : Int) : List Instr :=
  [.mov .rax (.mem (ix x .r12 (8 * (a + 1)))), .mov .rdx (.mem (ix x .r12 (8 * a))), .shld .rax .rdx 63,
    .store { base := t, disp := 8 * o } .rax]

/-- `q̂` into `sU`: the 3-by-2 estimate of `⌊R / 2⌋`'s top three words by `s`'s top two. -/
def estX : List Instr :=
  ws ++ base sqU .rsi ++ base sqS .r11 ++ winPtrs ++
  half .rbx .rsi (-4) 0 ++ half .rbx .rsi (-3) 1 ++ half .rbx .rsi (-2) 2 ++
  half .r10 .r11 (-4) 1 ++ half .r10 .r11 (-3) 2 ++
  ([.mov .rbx (.reg .rsi), .mov .r10 (.reg .r11), .mov .rbp (.reg .r11), .mov32 .r12 (.imm 3)] : List Instr) ++
  R2Words.quot ++ R2Words.refine3 ++ ([.store (hdr sU) .rcx] : List Instr)

/-- Word `i` of `[rbx] - rcx [r10]`, the product's carry in `r9` and the borrow in `rbp`. -/
def msBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .mul .rcx, .alu .add .rax (.reg .r9), .alu .adc .rdx (.imm 0),
    .mov .r9 (.reg .rdx), .mov .rdx (.mem (ix .rbx .r14)), cfFromRbp, .alu .sbb .rdx (.reg .rax), cfToRbp,
    .store (ix .rbx .r14) .rdx]

/-- `D`'s word `m := q̂`; `T := R - q̂ D` over the window. -/
def mulSubX : Prog isa :=
  .seq (.block (winPtrs ++ ([.mov .rcx (.mem (hdr sU)), .store (at0 .r10) .rcx, .mov32 .r9 (.imm 0),
    .mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 msBody)

/-- `D`'s low two words `(y₁, q̂)` to `E = (y₁, 0) + 2 q̂ - 1` modulo `2^128`, so that
`D` is `E = 2 s β + 2 q̂ - 1`, a correction's addend. -/
def toE : List Instr :=
  winPtrs ++ ([.mov .rax (.mem (at0 .r10)), .alu .add .rax (.reg .rax), .mov .rdx (.mem { base := .r10, disp := 8 }),
    .alu .adc .rdx (.imm 0), .alu .sub .rax (.imm 1), .alu .sbb .rdx (.imm 0), .store (at0 .r10) .rax,
    .store { base := .r10, disp := 8 } .rdx] : List Instr)

/-- If `T < 0`: `T := T + E` and `E := E - 2` (`q̂ := q̂ - 1`). -/
def fixX : Prog isa :=
  .seq (.seq (.block (winPtrs ++ ([.mov .rax (.mem (ix .rbx .r12 (-8))), .alu .add .rax (.reg .rax),
      .alu .sbb .r15 (.reg .r15), .mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 addMBody))
    (.block [.mov .r11 (.reg .r15), .alu .and .r11 (.imm 2), .mov .rax (.mem (at0 .r10)),
      .mov .rdx (.mem { base := .r10, disp := 8 }), .alu .sub .rax (.reg .r11), .alu .sbb .rdx (.imm 0),
      .store (at0 .r10) .rax, .store { base := .r10, disp := 8 } .rdx])

/-- `D := E + 1 = 2 s β + 2 q̂`, which is `2 s' β^m` for the new root `s' = s β + q̂`. -/
def updX : List Instr :=
  winPtrs ++ ([.mov .rax (.mem (at0 .r10)), .mov .rdx (.mem { base := .r10, disp := 8 }), .alu .add .rax (.imm 1),
    .alu .adc .rdx (.imm 0), .store (at0 .r10) .rax, .store { base := .r10, disp := 8 } .rdx] : List Instr)

def stepX : Prog isa := seqs [.block estX, mulSubX, .block toE, fixX, fixX, fixX, .block updX, .block countNext]

/-- `[t] := [j] / 2` (`[t]` cleared above). -/
def halfA (t j : Nat) : Prog isa := .seq (.block (ws ++ base j .r8 ++ base t .rsi)) (wordLoop 0 shrBody)

/-- A stage of `c` words of the root's shift `⌊K / 2⌋`, where `c ≤ 2 h`. -/
def stageR (c : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 4)))] : List Instr)))
    (.ite .b (.block []) (seqs ([.block [.mov .rax (.mem (hdr sK2)), .alu .and .rax (.imm (BitVec.ofNat 32 c)),
      .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .store (hdr sB2) .rax]] ++
      shrWords sqR c sqT ++ [selK false sqR sqT])))

/-- The remainder's zero test into the mask; the root `s = D / 2` shifted right by
`c = 32 K + z / 2`, into 2, less one if `X` was zero. -/
def finishX : List (Prog isa) :=
  [.seq (.block (ws ++ base sqZ .rbx ++ ([.mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 or1Body),
   .block CrtValues.andZero, zeroA sqR, halfA sqR sqD,
   .block [.mov .rax (.mem (hdr sK2)), .mov .rdx (.reg .rax), .shift .shr .rax 1, .store (hdr sK2) .rax,
     .alu .and .rdx (.imm 1), .shift .shl .rdx 5, .mov .rax (.mem (hdr sC)), .shift .shr .rax 1,
     .alu .add .rax (.reg .rdx), .store (hdr sC) .rax]] ++
  wordStages.map stageR ++ [shrZ sqR sqT, copyA sqR sqT,
   .block (ws ++ base sqR .rbx ++ ([.mov .rax (.mem (hdr sZ)), .alu .and .rax (.imm 1), .mov .rdx (.mem (at0 .rbx)),
     .alu .sub .rdx (.reg .rax), .store (at0 .rbx) .rdx] : List Instr))]

/-- `y = ⌊√X⌋` into wide 2 (narrow 4), and the mask cleared unless `X = y²`. -/
def sqrt : List (Prog isa) := normX ++ firstX ++
  [.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr)), .loop stepX .ne] ++ finishX

/-! ## The factors (narrow) -/

def factors : List (Prog isa) := [zeroA 10, addA 10 8 4, shrA 10, zeroA 11, subA 11 8 4, shrA 11] ++
  storeA 10 sP sK sMask ++ storeA 11 sQ sK sMask ++ [.block retMask]

/-! ## The function -/

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([.block head] ++ loadA aN sN sK ++ [zeroA 1] ++ loadA aE sE sElen ++ loadA aD sD sDl ++
  prod ++ [.block (width true)] ++ deMinus ++
  [.block (width false)] ++ twosInit ++ twos ++ [gcdW 6 12 7] ++
  [.block (width true)] ++ divA ++ divB ++ minus4n ++ sqrt ++ [.block (width false)] ++ factors)

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa :=
  .seq (.block (Recover.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid))
    (.ite .ne Recover.fail main)

end VG.Impl.Rsa.X86_64.Keys.RecoverDet
