module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs

/-!
# The batched inverse modulo an odd number, on RISC-V

`inverse`: the inverse of `x` modulo an odd `m`, and `gcd(x, m)`, by batches
of 59 divsteps (Bernstein and Yang) on 64-bit words, as x86-64's
(`Impl/Rsa/X86_64/Keys.lean`'s `Inv`), in the key operations' arrays
(`KeyWs.lean`). The caller gives `n` in `s8` in digits of 32 bits (at most
twice the working space's `w` words), `x` in array 0 and `m` in array 8, both
below `2^(32 n)`; the inverse works on `ν = ⌈n / 2⌉` words. Array 1 ends as
`gcd(x, m)` and array 3 as `y < m` with `y x ≡ gcd(x, m) (mod m)` (for
`m > 1`), `w` words each.

The state of `Proof/Divstep/TcS.lean`'s `invRunS 59`: `f` and `g` in arrays 4
and 5, `ν + 1` words in two's complement; the coefficients `a`, `b` in arrays
6 and 7, `ν + 1` words in two's complement, in `(-m, 2m)` (reduced only at the
end); `m` with a zero word `ν` in array 2; `d`, the batch's matrix and
`-m⁻¹ mod 2^64` in words of array 9 (the window). Each batch runs 59 divsteps
on the low words of `f` and `g` (`Proof/Divstep/WordDef.lean`'s `wstep`,
unrolled, in `t0`–`t6`, `a4`, `a5` and `a7`), then two passes over the
words, as libsecp256k1's `update_fg` and `update_de`, each in place:

* `updateG`: the new `f` and `g`, `(u f + v g) / 2^59` and
  `(q f + r g) / 2^59`, both from one read of each word: two signed 128-bit
  accumulators, a product's low word by `mul` and its high word by `mulhu`
  less the word where the coefficient is negative (the model has no
  `mulhsu`), and each low word, with the top five bits of the one before,
  stored a word down;
* `updateAB`: the new `a` and `b`, `(t + k m) / 2^64` for
  `t = u a + v b` and `q a + r b` and `k = t₀ (-m⁻¹) mod 2^64`, with `k m`
  added to each low word by an unsigned carry, the sum stored a word down.

Both borrow twelve registers (`spill1`, `spill2`), kept in arrays 11 and 12.

`n` stays in `s8` and the count of the batches left in `s7`, so every loop's
count and every address depends only on `w`, `n` and the base, all in
registers, and every choice is a masked selection. After `3 ν + 2` batches
(`177 ν + 118` divsteps), `a` is brought into `[0, m)`, negated if `f < 0` and
doubled `5 (3 ν + 2)` times modulo `m` (each batch scaled it by `2^(59 - 64)`),
and `|f|` is the gcd.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.InvBatch

open VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys

/-! ## The arrays and the window -/

def aX : Nat := 0
def aGcd : Nat := 1
def aMz : Nat := 2
def aY : Nat := 3
def aF : Nat := 4
def aG : Nat := 5
def aA : Nat := 6
def aB : Nat := 7
def aMin : Nat := 8
def aW : Nat := 9
def aT1 : Nat := 11
def aT2 : Nat := 12
def aT3 : Nat := 13

/-- The window's words: `d`, the matrix `u v q r`, and `-m⁻¹ mod 2^64`. -/
def wD : Nat := 0
def wU : Nat := 8
def wV : Nat := 16
def wQ : Nat := 24
def wR : Nat := 32
def wIv : Nat := 40

/-- `t3 := ν = ⌈n / 2⌉`, the words. -/
def cntN : List Instr := [.addi .t3 .s8 1, .shift .srl .d .t3 .t3 1]

/-- `t3 := ν + 1`. -/
def cntN1 : List Instr := cntN ++ [.addi .t3 .t3 1]

/-- The window's word at `o` into `r`. -/
def ldW (r : Reg) (o : Nat) : List Instr := ptr r aW ++ [.load .d r r o]

/-- `t1 :=` the address of word `ν` of `[j]`. -/
def topOf (j : Nat) : List Instr := ptr .t1 j ++ cntN ++ [.shift .sll .d .t3 .t3 3, .add .t1 .t1 .t3]

/-! ## The word loops -/

/-! `Keys`' `subBody`, `selBody` and `copyBody` (`KeyWs.lean`) are the
word loops' bodies. -/

/-- The words `[j]` (`t3` of them, from `t0`) zeroed. -/
def zeros : Prog isa := .seq (.block [.li .t5 0]) (countLoop .t3 [.store .d .t5 .t0 0, .addi .t0 .t0 8])

/-- One word of `[a] + k [b]` (`k` in `a5`), the carry in and out in `t4`, to
`[o]`, through `t5`, `t6` and `a4`. -/
def macBody : List Instr :=
  [.load .d .t5 .t2 0, .mul .t6 .a5 .t5, .mulhu .t5 .a5 .t5, .load .d .a4 .t1 0, .add .t6 .t6 .a4,
    .sltu .a4 .t6 .a4, .add .t5 .t5 .a4, .add .t6 .t6 .t4, .sltu .a4 .t6 .t4, .add .t4 .t5 .a4,
    .store .d .t6 .t0 0, .addi .t0 .t0 8, .addi .t1 .t1 8, .addi .t2 .t2 8]

/-- The pointers of `[o] = [a] + k [b]`, the count `cnt` and no carry. -/
def macSetup (o a b : Nat) (cnt : List Instr) : List Instr :=
  ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ cnt ++ [.li .t4 0]

/-- `[o] = [a] + k [b]`, `cnt` words, the carry out in `t4`. -/
def mac (o a b : Nat) (cnt : List Instr) : Prog isa := .seq (.block (macSetup o a b cnt)) (countLoop .t3 macBody)

/-! ## The divsteps -/

/-- One divstep on words, `wstep`, with `d f g u v q r` in `t6`, `a4`, `t0`–`t4`:
`t5` holds `g`'s parity and the masked terms, `a5` the mask of an odd `g`,
`a7` the mask of a swap. -/
def wstepCode : List Instr :=
  [.logicImm .and .t5 .t0 1, .li .a5 0, .sub .a5 .a5 .t5,
    .shift .srl .d .a7 .t6 63, .addi .a7 .a7 (-1), .logic .and .a7 .a7 .a5,
    .logic .xor .t5 .a4 .a7, .sub .t5 .t5 .a7, .logic .and .t5 .t5 .a5, .add .t0 .t0 .t5,
    .logic .xor .t5 .t1 .a7, .sub .t5 .t5 .a7, .logic .and .t5 .t5 .a5, .add .t3 .t3 .t5,
    .logic .xor .t5 .t2 .a7, .sub .t5 .t5 .a7, .logic .and .t5 .t5 .a5, .add .t4 .t4 .t5,
    .logic .xor .t6 .t6 .a7, .sub .t6 .t6 .a7, .addi .t6 .t6 2,
    .logic .and .t5 .t0 .a7, .add .a4 .a4 .t5,
    .shift .srl .d .t0 .t0 1,
    .logic .and .t5 .t3 .a7, .add .t1 .t1 .t5, .add .t1 .t1 .t1,
    .logic .and .t5 .t4 .a7, .add .t2 .t2 .t5, .add .t2 .t2 .t2]

/-- `k` divsteps, unrolled. -/
def wsteps (k : Nat) : List Instr := (List.replicate k wstepCode).flatten

/-- The low words of `f` and `g`, `d`, and the identity matrix. -/
def start : List Instr :=
  ptr .t0 aF ++ [.load .d .a4 .t0 0] ++ ptr .t0 aG ++ [.load .d .t0 .t0 0] ++ ldW .t6 wD ++
    [.li .t1 1, .li .t2 0, .li .t3 0, .li .t4 1]

/-- `d` and the matrix to the window. -/
def save : List Instr :=
  ptr .a4 aW ++ [.store .d .t6 .a4 wD, .store .d .t1 .a4 wU, .store .d .t2 .a4 wV,
    .store .d .t3 .a4 wQ, .store .d .t4 .a4 wR]

/-! ## The array operations -/

/-- A signed coefficient `c` (in `cr`, its sign's mask in `mr`) times the
word `x`, added to the signed accumulator `(lo, hi)`: the low word by `mul`,
the high word by `mulhu` less `x` if `c < 0`, through `p`. -/
def term (cr mr x lo hi p : Reg) : List Instr :=
  [.mul p cr x, .add lo lo p, .sltu p lo p, .add hi hi p, .mulhu p cr x, .add hi hi p,
    .logic .and p mr x, .sub hi hi p]

/-! ### The pass over `f` and `g`

`u`, `v`, `q`, `r` in `a5`, `a7`, `s1`, `s2` and their signs' masks in
`s3`–`s6`; the pointers at word `i - 1` of `f` and `g` in `t0` and `t1`, and
word `i` read into `t5` and `t6`; `u f + v g` accumulated in `(t4, a4)` and
`q f + r g` in `(a0, a1)`, signed, through `t2`; and the top five bits of
their last low words in `a2` and `a3`. Each low word, with the five bits of
the one before, is word `i - 1` of the new `f` or `g`, in place. -/

/-- Word `i` of `f` and `g` at offset `o` of the pointers, into both
accumulators. -/
def fgHead (o : Nat) : List Instr :=
  [.load .d .t5 .t0 o, .load .d .t6 .t1 o] ++ term .a5 .s3 .t5 .t4 .a4 .t2 ++ term .a7 .s4 .t6 .t4 .a4 .t2 ++
    term .s1 .s5 .t5 .a0 .a1 .t2 ++ term .s2 .s6 .t6 .a0 .a1 .t2

/-- The low words' top five bits kept, and the accumulators shifted down a
word. -/
def fgShift : List Instr :=
  [.shift .srl .d .a2 .t4 59, .addi .t4 .a4 0, .shift .sra .d .a4 .a4 63,
    .shift .srl .d .a3 .a0 59, .addi .a0 .a1 0, .shift .sra .d .a1 .a1 63]

/-- Word `i - 1` of the new `f` and `g`: the five bits before and the low
word's low 59. -/
def fgOut : List Instr :=
  [.shift .sll .d .t2 .t4 5, .add .t2 .a2 .t2, .store .d .t2 .t0 0,
    .shift .sll .d .t2 .a0 5, .add .t2 .a3 .t2, .store .d .t2 .t1 0]

/-- A word `i ≥ 1`. -/
def fgBody : List Instr := fgHead 8 ++ fgOut ++ fgShift ++ [.addi .t0 .t0 8, .addi .t1 .t1 8]

/-- The new `f`'s and `g`'s top words: the last five bits, sign-extended. -/
def fgTop : List Instr :=
  [.shift .sll .d .t2 .a2 59, .shift .sra .d .t2 .t2 59, .store .d .t2 .t0 0,
    .shift .sll .d .t2 .a3 59, .shift .sra .d .t2 .t2 59, .store .d .t2 .t1 0]

/-- The matrix from the window, `u`, `v`, `q`, `r` into `a5`, `a7`, `s1`,
`s2`. -/
def ldMat : List Instr := ldW .a5 wU ++ ldW .a7 wV ++ ldW .s1 wQ ++ ldW .s2 wR

/-- The pass's start: the matrix and three of its masks (`s3`–`s5`), the
pointers at `[a]` and `[b]` in `t0` and `t1`, the accumulators zero. -/
def passSetup (a b : Nat) : List Instr :=
  ldMat ++ [.shift .sra .d .s3 .a5 63, .shift .sra .d .s4 .a7 63, .shift .sra .d .s5 .s1 63] ++
    ptr .t0 a ++ ptr .t1 b ++ [.li .t4 0, .li .a4 0, .li .a0 0, .li .a1 0]

/-- The registers `rs` stored to the words from `o` at `t0`. -/
def stD : List Reg → Nat → List Instr
  | [], _ => []
  | r :: rs, o => .store .d r .t0 o :: stD rs (o + 8)

/-- And loaded from them. -/
def ldD : List Reg → Nat → List Instr
  | [], _ => []
  | r :: rs, o => .load .d r .t0 o :: ldD rs (o + 8)

/-- The halves of `spill1` and `spill2`, kept in arrays 11 and 12. -/
def spill1 : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5]
def spill2 : List Reg := [.s6, .a0, .a1, .a2, .a3, .a6]

/-- `spill1` and `spill2` to the first six words of arrays 11 and 12. -/
def spill : List Instr := ptr .t0 aT1 ++ stD spill1 0 ++ ptr .t0 aT2 ++ stD spill2 0

/-- And back. -/
def restore : List Instr := ptr .t0 aT1 ++ ldD spill1 0 ++ ptr .t0 aT2 ++ ldD spill2 0

/-- The new `f` and `g`, `(u f + v g) / 2^59` and `(q f + r g) / 2^59`, in
place, `ν + 1` words: word 0 into the accumulators, then `ν` words, then the
top words. -/
def updateG : Prog isa := seqs [
  .block (spill ++ passSetup aF aG ++ [.shift .sra .d .s6 .s2 63] ++ fgHead 0 ++ fgShift ++ cntN),
  countLoop .t3 fgBody, .block (fgTop ++ restore)]

/-! ### The pass over `a` and `b`

As over `f` and `g`, with `m` (array 2, its word `ν` zero) at word `i - 1` in
`t2`, and `t2`'s role as the products' register taken by `s6`. `r`'s mask
is made at each word (`s6`), for want of a register. The low words `t` of
`u a + v b` and `q a + r b` from word 0 make `k₁ = t (-m⁻¹)` and `k₂` (`a2`,
`a3`), and from each word on `k m` is added to the accumulator's low word
with an unsigned carry (`a6`, `s0`), as `mac`: so word 0 of each sum is zero
and word `i` is word `i - 1` of `(t + k m) / 2^64`, in place. At the top
word, where `m`'s is zero, the sum's word `ν + 1` is the sign of the low
word `t` (as a number of `ν + 1` words) and the carry. -/

/-- `term` with `r`'s mask made from `s2`. -/
def termR : List Instr :=
  [.mul .s6 .s2 .t6, .add .a0 .a0 .s6, .sltu .s6 .a0 .s6, .add .a1 .a1 .s6, .mulhu .s6 .s2 .t6,
    .add .a1 .a1 .s6, .shift .sra .d .s6 .s2 63, .logic .and .s6 .s6 .t6, .sub .a1 .a1 .s6]

/-- Word `i` of `a` and `b` at offset `o` of the pointers, into both
accumulators. -/
def abHead (o : Nat) : List Instr :=
  [.load .d .t5 .t0 o, .load .d .t6 .t1 o] ++ term .a5 .s3 .t5 .t4 .a4 .s6 ++ term .a7 .s4 .t6 .t4 .a4 .s6 ++
    term .s1 .s5 .t5 .a0 .a1 .s6 ++ termR

/-- `k m_i` (`m_i` in `t5`) added to the low word `lo`, with the carry `c`,
through `s6` and `t6`, as `macBody`. -/
def macW (k lo c : Reg) : List Instr :=
  [.mul .s6 k .t5, .add .s6 .s6 lo, .sltu lo .s6 lo, .mulhu .t6 k .t5, .add .t6 .t6 lo, .add lo .s6 c,
    .sltu .s6 lo c, .add c .t6 .s6]

/-- The accumulators shifted down a word. -/
def abShift : List Instr :=
  [.addi .t4 .a4 0, .shift .sra .d .a4 .a4 63, .addi .a0 .a1 0, .shift .sra .d .a1 .a1 63]

/-- Word 0: `k₁` and `k₂` from the low words and `-m⁻¹` (the window's), and
`k m₀` added. -/
def abFirst : List Instr :=
  abHead 0 ++ ldW .t5 wIv ++ [.mul .a2 .t4 .t5, .mul .a3 .a0 .t5, .load .d .t5 .t2 0] ++
    macW .a2 .t4 .a6 ++ macW .a3 .a0 .s0 ++ abShift

/-- A word `1 ≤ i < ν`. -/
def abBody : List Instr :=
  abHead 8 ++ [.load .d .t5 .t2 8] ++ macW .a2 .t4 .a6 ++ [.store .d .t4 .t0 0] ++ macW .a3 .a0 .s0 ++
    [.store .d .a0 .t1 0] ++ abShift ++ [.addi .t0 .t0 8, .addi .t1 .t1 8, .addi .t2 .t2 8]

/-- Word `ν`, where `m`'s is zero: the low words with the carries are words
`ν - 1`, and the low words' signs with the carries out words `ν`. -/
def abLast : List Instr :=
  abHead 8 ++ [.shift .sra .d .t5 .t4 63, .add .t4 .t4 .a6, .sltu .t6 .t4 .a6, .store .d .t4 .t0 0,
    .add .t5 .t5 .t6, .store .d .t5 .t0 8,
    .shift .sra .d .t5 .a0 63, .add .a0 .a0 .s0, .sltu .t6 .a0 .s0, .store .d .a0 .t1 0,
    .add .t5 .t5 .t6, .store .d .t5 .t1 8]

/-- The new `a` and `b`, `(t + k m) / 2^64` for `t = u a + v b` and
`q a + r b`, in place, `ν + 1` words: word 0, then words `1 … ν - 1`, then
word `ν`. -/
def updateAB : Prog isa := seqs [
  .block (spill ++ passSetup aA aB ++ ptr .t2 aMz ++ [.li .a6 0, .li .s0 0] ++ abFirst ++ cntN ++
    [.addi .t3 .t3 (-1)]),
  .ite (.zero .t3) (.block []) (countLoop .t3 abBody), .block (abLast ++ restore)]

/-- `[o] = [x] - m` where that does not borrow, else `[x]`, `ν + 1` words:
the difference into `[s]`, then selected by the borrow. -/
def csub (o x s : Nat) : Prog isa := seqs [
  .block (ptr .t0 s ++ ptr .t1 x ++ ptr .t2 aMz ++ cntN1 ++ [.li .t4 0]), countLoop .t3 subBody,
  .block (ptr .t0 o ++ ptr .t1 s ++ ptr .t2 x ++ cntN1 ++ [.li .t5 0, .sub .t4 .t5 .t4]),
  countLoop .t3 selBody]

/-- The new `f`, `g`, `a` and `b`. -/
def update : Prog isa := .seq updateG updateAB

/-- A batch, and the count of those left decremented. -/
def batch : Prog isa := seqs [.block (start ++ wsteps 59 ++ save), update, .block [.addi .s7 .s7 (-1)]]

/-- A batch of `f` and `g` alone. -/
def batchG : Prog isa := seqs [.block (start ++ wsteps 59 ++ save), updateG, .block [.addi .s7 .s7 (-1)]]

/-! ## The start -/

/-- A Newton step of the inverse modulo powers of 2: `x := x (2 - m x)`, `m` in
`t5` and `x` in `t6`, through `a5` and `t4`. -/
def newton : List Instr := [.mul .a5 .t5 .t6, .li .t4 2, .sub .a5 .t4 .a5, .mul .t6 .t6 .a5]

/-- `init`'s first part: `[2] = m` with a zero word `ν`. -/
def initA : Prog isa := seqs [
  .seq (.block (ptr .t0 aMz ++ ptr .t1 aMin ++ cntN)) (countLoop .t3 copyBody),
  .block (topOf aMz ++ [.li .t5 0, .store .d .t5 .t1 0])]

/-- `init`'s second part: `-m⁻¹ mod 2^64` to the window, from `m`'s low word
`m₀`: `m₀` is its own inverse modulo `2^3` (an odd square is 1 modulo 8),
and five Newton steps make it right modulo `2^96`. -/
def initB : Prog isa :=
  .block (ptr .a4 aMz ++ [.load .d .t5 .a4 0, mov .t6 .t5] ++ newton ++ newton ++ newton ++ newton ++ newton ++
    [.li .a5 0, .sub .t1 .a5 .t6] ++ ptr .a4 aW ++ [.store .d .t1 .a4 wIv])

/-- `init`'s third part: `f = m`, `g = x + m` if `x` is even, else `x`,
`(a, b) = (0, 1)`, `d = 1`, and `3 ν + 2` batches to run. -/
def initC : Prog isa := seqs [
  .seq (.block (ptr .t0 aF ++ ptr .t1 aMz ++ cntN1)) (countLoop .t3 copyBody),
  .block (ptr .t0 aX ++ [.load .d .a5 .t0 0, .logicImm .and .a5 .a5 1, .logicImm .xor .a5 .a5 1]),
  mac aG aX aMz cntN,
  .block [.store .d .t4 .t0 0],
  .seq (.block (ptr .t0 aA ++ cntN1)) zeros,
  .seq (.block (ptr .t0 aB ++ cntN1)) zeros,
  .block (ptr .t0 aB ++ [.li .t5 1, .store .d .t5 .t0 0] ++ ptr .t0 aW ++ [.store .d .t5 .t0 wD] ++ cntN ++
    [.add .s7 .t3 .t3, .add .s7 .s7 .t3, .addi .s7 .s7 2])]

/-- The start: `[2] = m`, its word `ν` zero; `-m⁻¹ mod 2^64` to the window;
`f = m`, `g = x + m` if `x` is even, else `x`; `(a, b) = (0, 1)`, `d = 1`;
and `3 ν + 2` batches to run. -/
def init : Prog isa := .seq initA (.seq initB initC)

/-! ## The end -/

/-- The mask of `[j]`'s sign (its word `ν`'s bit 63) into `t4`. -/
def signOf (j : Nat) : List Instr := topOf j ++ [.load .d .t4 .t1 0, .shift .sra .d .t4 .t4 63]

/-- `[o] = [b]` if `[j] < 0`, else `[a]`, `ν + 1` words. -/
def signSel (j o a b : Nat) : Prog isa :=
  .seq (.block (signOf j ++ ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ cntN1)) (countLoop .t3 selBody)

/-- `a` from `(-m, 2m)` into `[0, m)`: `a + m` if `a < 0`, then less `m` if
that does not borrow. -/
def reduce : Prog isa := seqs [
  .block [.li .a5 1], mac aT3 aA aMz cntN1, signSel aA aA aA aT3, csub aA aA aT1]

/-- `a` into `[0, m)`, then `a := (m - a) mod m` if `f < 0`. -/
def normalize : Prog isa := seqs [
  reduce,
  .block (ptr .t0 aT3 ++ ptr .t1 aMz ++ ptr .t2 aA ++ cntN1 ++ [.li .t4 0]), countLoop .t3 subBody,
  signSel aF aA aA aT3, csub aA aA aT1]

/-- `a := 2 a mod m`. -/
def double : Prog isa := seqs [
  .block [.li .a5 1], mac aT3 aA aA cntN1, csub aA aT3 aT1]

/-- `5 (3 ν + 2)` doublings, counted in `s7`. -/
def doublings : Prog isa :=
  .seq (.block (cntN ++ [.shift .sll .d .s7 .t3 4, .sub .s7 .s7 .t3, .addi .s7 .s7 10]))
    (.loop (.seq double (.block [.addi .s7 .s7 (-1)])) (.nonzero .s7))

/-- `[j]`'s `w + 1` words zeroed. -/
def zeroW (j : Nat) : Prog isa := .seq (.block (ptr .t0 j ++ [.addi .t3 .s9 1])) zeros

/-- `[1] = |f|`. -/
def finishG : Prog isa := seqs [
  zeroW aGcd,
  .block (ptr .t0 aT1 ++ ptr .t1 aGcd ++ ptr .t2 aF ++ cntN1 ++ [.li .t4 0]), countLoop .t3 subBody,
  signSel aF aGcd aF aT1]

/-- `[3] = a`. -/
def finishY : Prog isa := seqs [
  zeroW aY,
  .block (ptr .t0 aY ++ ptr .t1 aA ++ cntN1), countLoop .t3 copyBody]

/-- `[1] = |f|` and `[3] = a`. -/
def finish : Prog isa := .seq finishG finishY

/-- `gcd(x, m)` alone into array 1. -/
def gcd : Prog isa := seqs [init, .loop batchG (.nonzero .s7), finishG]

/-- The inverse at the working space's width `w` (`s9`). -/
def inverse : Prog isa := seqs [init, .loop batch (.nonzero .s7), normalize, doublings, finish]

/-- The inverse without its doublings: `[3] = y` with
`y 2^(5 (3 ν + 2)) x ≡ gcd(x, m) (mod m)`, for a caller that scales `y` itself. -/
def inverseS : Prog isa := seqs [init, .loop batch (.nonzero .s7), normalize, finish]

end VG.Impl.Rsa.RISCV64.InvBatch
