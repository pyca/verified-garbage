module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs

/-!
# The batched inverse modulo an odd number, on PPC64LE

`inverse`: the inverse of `x` modulo an odd `m`, and `gcd(x, m)`, by batches
of 59 divsteps (Bernstein and Yang) on 64-bit words, as RISC-V's
(`Impl/Rsa/RISCV64/InvBatch.lean`), in the key operations' arrays
(`KeyWs.lean`). The caller gives `n` in `r11` in digits of 32 bits (`n ≤ w`,
the working space's digits), `x` in array 0 and `m` in array 8, both below
`2^(32 n)`; the inverse works on `ν = ⌈n / 2⌉` words. Array 1 ends as
`gcd(x, m)` and array 3 as `y < m` with `y x ≡ gcd(x, m) (mod m)` (for
`m > 1`), `ν + 1` words each after `w + 2` digits zeroed. `gcd` leaves only
`gcd(x, m)` in array 1: its batches update `f` and `g` alone (`batchG`), and it
has neither the reduction of `a` nor its doublings.

The state of `Proof/Divstep/TcS.lean`'s `invRunS 59`: `f` and `g` in arrays 4
and 5, `ν + 1` words in two's complement; the coefficients `a`, `b` in arrays
6 and 7, `ν + 1` words in two's complement, in `(-m, 2m)` (reduced only at the
end); `m` with a zero word `ν` in array 2; `d`, the batch's matrix and
`-m⁻¹ mod 2^64` in words of array 14 (the window). Each batch runs 59
divsteps on the low words of `f` and `g` (`Proof/Divstep/WordDef.lean`'s
`wstep`, unrolled, in `r3`–`r9` with `r0`, `r11`, `r12`), then updates `f`,
`g` and `a`, `b` in place, one pass over the words of each pair (`updateG`,
`updateAB`), both rows of the matrix at once: `u x + v y` and `q x + r y`
accumulated in two signed 128-bit accumulators, each product's low word by
`mul` and its high word by `mulhu` less the word where the coefficient is
negative (its sign's mask; the model has no signed high product), the carries
by the carry bit (`addc`, `adde`):

* over `f` and `g`: the low words shifted by 59 stored a word down, and the
  last five bits, sign-extended, as word `ν`;
* over `a` and `b`: `k = t₀ (-m⁻¹) mod 2^64` of each row's word 0, `k m_i`
  added to its word `i` with an unsigned carry and stored a word down (word 0
  of the sum is zero), and at word `ν` (`m`'s is zero) the low word with the
  carry and its sign with the carry out as words `ν - 1` and `ν` (the arrays
  have room for `ν + 1` words when `n = w`, not `ν + 2`).

The passes borrow `r14`–`r28`, saved to the first words of arrays 11–13 for
each batch (`spill`, `restore`).

`n` and the count of the batches left share `r10`: `n` in its low 15 bits, the
count above. So every loop's count and every address depends only on `n`,
`w` and the base, all in registers, and every choice is a masked selection.
After `3 ν + 2` batches (`177 ν + 118` divsteps), `a` is brought into
`[0, m)`, negated if `f < 0` and doubled `5 (3 ν + 2)` times modulo `m` (each
batch scaled it by `2^(59 - 64)`), and `|f|` is the gcd; `inverseS` leaves
the doublings to its caller.
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.InvBatch

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys

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
def aT1 : Nat := 11
def aT2 : Nat := 12
def aT3 : Nat := 13
def aW : Nat := 14

/-- The window's 64-bit words: `d`, the matrix `u v q r`, and `-m⁻¹ mod 2^64`. -/
def wD : Nat := 0
def wU : Nat := 8
def wV : Nat := 16
def wQ : Nat := 24
def wR : Nat := 32
def wIv : Nat := 40

/-- `r8 := ν = ⌈n / 2⌉`, for `n` the low 15 bits of `r10`. -/
def cntN : List Instr := [.lsl .r8 .r10 49, .lsr .d .r8 .r8 49, .addi .r8 .r8 1, .lsr .d .r8 .r8 1]

/-- `r8 := ν + 1`. -/
def cntN1 : List Instr := cntN ++ [.addi .r8 .r8 1]

/-- The window's word at `o` into `r`. -/
def ldW (r : Reg) (o : Nat) : List Instr := ptr r aW ++ [.load .d r r o]

/-- `r6 :=` the address of word `ν` of `[j]`. -/
def topOf (j : Nat) : List Instr := ptr .r6 j ++ cntN ++ [.lsl .r8 .r8 3, .add .r6 .r6 .r8]

/-! ## The word loops -/

/-- The words from `r5` (`r8` of them) zeroed (`r0 = 0`). -/
def zerosW : Prog isa := countLoop .r8 [.store .d .r0 .r5 0, .addi .r5 .r5 8]

/-- One digit of `[a] + k [b]` (`k < 2^32` in `r11`), the carry in `r9`: the
sum is below `2^64`. `MontKey`'s products by digits. -/
def macBody : List Instr :=
  [.load .w .r0 .r7 0, .mul .r0 .r11 .r0, .load .w .r3 .r6 0, .add .r0 .r0 .r3, .add .r0 .r0 .r9,
    .store .w .r0 .r5 0, .lsr .d .r9 .r0 32, .addi .r5 .r5 4, .addi .r6 .r6 4, .addi .r7 .r7 4]

/-- One word of `[a] + k [b]` (`k` in `r11`), the carry in and out in `r9`, to
`[o]`, through `r0`, `r3` and `r12`: the sum is below `2^128`. -/
def macWBody : List Instr :=
  [.load .d .r0 .r7 0, .mul .r3 .r11 .r0, .mulhu .r0 .r11 .r0, .load .d .r12 .r6 0, .addc .r3 .r3 .r12,
    .addze .r0 .r0, .addc .r3 .r3 .r9, .addze .r9 .r0, .store .d .r3 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8,
    .addi .r7 .r7 8]

/-- `[o] = [a] + k [b]`, `cnt` words, the carry out in `r9`. -/
def mac (o a b : Nat) (cnt : List Instr) : Prog isa :=
  .seq (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cnt ++ [.li .r9 0])) (countLoop .r8 macWBody)

/-- `[o] = [a] - [b]`, `ν + 1` words, the carry bit set where it does not borrow. -/
def subW (o a b : Nat) : Prog isa :=
  .seq (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cntN1 ++ [.subc .r0 .r8 .r8])) (countLoop .r8 subWBody)

/-- `[o] = [x] - m` where that does not borrow, else `[x]`, `ν + 1` words:
the difference into `[s]`, then selected by the borrow (`CA - 1`, all ones
for a borrow). -/
def csub (o x s : Nat) : Prog isa := seqs [
  subW s x aMz,
  .block ([.li .r9 0, .adde .r9 .r9 .r9, .subi .r9 .r9 1] ++ ptr .r5 o ++ ptr .r6 s ++ ptr .r7 x ++ cntN1),
  countLoop .r8 selWBody]

/-! ## The divsteps -/

/-- One divstep on words, `wstep`, with `d f g u v q r` in `r3`–`r9`: `r0`
holds `g`'s parity and the masked terms, `r11` the mask of an odd `g`, `r12`
the mask of a swap. -/
def wstepCode : List Instr :=
  [.lsl .r0 .r5 63, .lsr .d .r0 .r0 63, .li .r11 0, .sub .r11 .r11 .r0,
    .lsr .d .r12 .r3 63, .subi .r12 .r12 1, .logic .and .r12 .r12 .r11,
    .logic .xor .r0 .r4 .r12, .sub .r0 .r0 .r12, .logic .and .r0 .r0 .r11, .add .r5 .r5 .r0,
    .logic .xor .r0 .r6 .r12, .sub .r0 .r0 .r12, .logic .and .r0 .r0 .r11, .add .r8 .r8 .r0,
    .logic .xor .r0 .r7 .r12, .sub .r0 .r0 .r12, .logic .and .r0 .r0 .r11, .add .r9 .r9 .r0,
    .logic .xor .r3 .r3 .r12, .sub .r3 .r3 .r12, .addi .r3 .r3 2,
    .logic .and .r0 .r5 .r12, .add .r4 .r4 .r0,
    .lsr .d .r5 .r5 1,
    .logic .and .r0 .r8 .r12, .add .r6 .r6 .r0, .add .r6 .r6 .r6,
    .logic .and .r0 .r9 .r12, .add .r7 .r7 .r0, .add .r7 .r7 .r7]

/-- `k` divsteps, unrolled. -/
def wsteps (k : Nat) : List Instr := (List.replicate k wstepCode).flatten

/-- The low words of `f` and `g`, `d`, and the identity matrix. -/
def start : List Instr :=
  ptr .r5 aF ++ [.load .d .r4 .r5 0] ++ ptr .r5 aG ++ [.load .d .r5 .r5 0] ++ ldW .r3 wD ++
    [.li .r6 1, .li .r7 0, .li .r8 0, .li .r9 1]

/-- `d` and the matrix to the window. -/
def save : List Instr :=
  ptr .r4 aW ++ [.store .d .r3 .r4 wD, .store .d .r6 .r4 wU, .store .d .r7 .r4 wV,
    .store .d .r8 .r4 wQ, .store .d .r9 .r4 wR]

/-! ## The array operations -/

/-! ## The updates

`u`, `v`, `q`, `r` in `r14`–`r17` and their signs' masks in `r18`–`r21`;
`u x + v y` accumulated in `(r22, r23)` and `q x + r y` in `(r24, r25)`; words
`i` of `x` and `y` in `r26`, `r27`, at offsets of `r5` and `r6`, the count in
`r8`. -/

/-- `c x` (`c` signed, its sign's mask in `m`) added to `(lo, hi)`, through `r3`. -/
def fterm (c m x lo hi : Reg) : List Instr :=
  [.mul .r3 c x, .addc lo lo .r3, .mulhu .r3 c x, .adde hi hi .r3, .logic .and .r3 m x, .sub hi hi .r3]

/-- Words `i` of `x` and `y` (at offset `o` of `r5`, `r6`) into both accumulators. -/
def fterms (o : Nat) : List Instr :=
  [.load .d .r26 .r5 o, .load .d .r27 .r6 o] ++ fterm .r14 .r18 .r26 .r22 .r23 ++ fterm .r15 .r19 .r27 .r22 .r23 ++
    fterm .r16 .r20 .r26 .r24 .r25 ++ fterm .r17 .r21 .r27 .r24 .r25

/-- An accumulator shifted down a word: its high word the low one, its sign the high one. -/
def fshift (lo hi : Reg) : List Instr := [.addi lo hi 0, .lsr .d .r0 hi 63, .li hi 0, .sub hi hi .r0]

/-- Word `i - 1` of `(x)/2^59` from the low word `lo` and the five bits `top` before it, at `p`. -/
def fout (lo top p : Reg) : List Instr := [.lsl .r3 lo 5, .add .r3 .r3 top, .store .d .r3 p 0, .lsr .d top lo 59]

/-- The registers `rs` stored to the words from `o` at `r3`. -/
def stRegs : List Reg → Nat → List Instr
  | [], _ => []
  | r :: rs, o => .store .d r .r3 o :: stRegs rs (o + 8)

/-- The registers `rs` loaded from the words from `o` at `r3`. -/
def ldRegs : List Reg → Nat → List Instr
  | [], _ => []
  | r :: rs, o => .load .d r .r3 o :: ldRegs rs (o + 8)

/-- The registers the passes borrow, saved to the first words of arrays 11,
12 and 13. -/
def spill1 : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19]
def spill2 : List Reg := [.r20, .r21, .r22, .r23, .r24, .r25]
def spill3 : List Reg := [.r26, .r27, .r28]

def spill : List Instr :=
  ptr .r3 aT1 ++ stRegs spill1 0 ++ ptr .r3 aT2 ++ stRegs spill2 0 ++ ptr .r3 aT3 ++ stRegs spill3 0

def restore : List Instr :=
  ptr .r3 aT1 ++ ldRegs spill1 0 ++ ptr .r3 aT2 ++ ldRegs spill2 0 ++ ptr .r3 aT3 ++ ldRegs spill3 0

/-- The matrix and its masks, the pointers at `[a]` and `[b]`, the accumulators zero. -/
def fsetup (a b : Nat) : List Instr :=
  ldW .r14 wU ++ ldW .r15 wV ++ ldW .r16 wQ ++ ldW .r17 wR ++
  [.li .r0 0, .lsr .d .r18 .r14 63, .sub .r18 .r0 .r18, .lsr .d .r19 .r15 63, .sub .r19 .r0 .r19,
    .lsr .d .r20 .r16 63, .sub .r20 .r0 .r20, .lsr .d .r21 .r17 63, .sub .r21 .r0 .r21] ++
  ptr .r5 a ++ ptr .r6 b ++ [.li .r22 0, .li .r23 0, .li .r24 0, .li .r25 0]

/-- A word `i ≥ 1` of `(f, g)`. -/
def fgBody : List Instr :=
  fterms 8 ++ fout .r22 .r28 .r5 ++ fout .r24 .r12 .r6 ++ fshift .r22 .r23 ++ fshift .r24 .r25 ++
    [.addi .r5 .r5 8, .addi .r6 .r6 8]

/-- The top words of the new `f` and `g`: the last five bits (`r28`, `r12`),
sign-extended, `t - 2^5 ⌊t / 2^4⌋`. -/
def fgTop : List Instr :=
  [.lsr .d .r0 .r28 4, .lsl .r0 .r0 5, .sub .r0 .r28 .r0, .store .d .r0 .r5 0,
    .lsr .d .r0 .r12 4, .lsl .r0 .r0 5, .sub .r0 .r12 .r0, .store .d .r0 .r6 0]

/-- The new `f` and `g`, `(u f + v g) / 2^59` and `(q f + r g) / 2^59`, in place. -/
def updateG : Prog isa := seqs [
  .block (fsetup aF aG ++ fterms 0 ++ [.lsr .d .r28 .r22 59, .lsr .d .r12 .r24 59] ++ fshift .r22 .r23 ++
    fshift .r24 .r25 ++ cntN),
  countLoop .r8 fgBody,
  .block fgTop]

/-- `k m_i` (`m_i` in `r4`) added to the low word `lo` with the carry `c`. -/
def fmac (k lo c : Reg) : List Instr :=
  [.mul .r3 k .r4, .addc .r3 .r3 lo, .mulhu .r0 k .r4, .addze .r0 .r0, .addc lo .r3 c, .addze c .r0]

/-- Word 0 of `(a, b)`, `iv` in `r4`: `k = t₀ iv` for each accumulator (`r28`,
`r12`), whose `k m₀` added makes the low words zero. -/
def abFirst : List Instr :=
  [.li .r9 0, .li .r11 0] ++ fterms 0 ++ [.mul .r28 .r22 .r4, .mul .r12 .r24 .r4, .load .d .r4 .r7 0] ++
    fmac .r28 .r22 .r9 ++ fmac .r12 .r24 .r11 ++ fshift .r22 .r23 ++ fshift .r24 .r25

/-- A word `1 ≤ i < ν` of `(a, b)`. -/
def abBody : List Instr :=
  fterms 8 ++ [.load .d .r4 .r7 8] ++ fmac .r28 .r22 .r9 ++ [.store .d .r22 .r5 0] ++ fmac .r12 .r24 .r11 ++
    [.store .d .r24 .r6 0] ++ fshift .r22 .r23 ++ fshift .r24 .r25 ++ [.addi .r5 .r5 8, .addi .r6 .r6 8, .addi .r7 .r7 8]

/-- Word `ν` (`m`'s is zero): the low words with the carries are words `ν - 1`,
the low words' signs with the carries out words `ν`. -/
def abLast : List Instr :=
  fterms 8 ++ [.lsr .d .r3 .r22 63, .li .r4 0, .sub .r3 .r4 .r3, .addc .r22 .r22 .r9, .addze .r3 .r3,
    .store .d .r22 .r5 0, .store .d .r3 .r5 8,
    .lsr .d .r3 .r24 63, .sub .r3 .r4 .r3, .addc .r24 .r24 .r11, .addze .r3 .r3,
    .store .d .r24 .r6 0, .store .d .r3 .r6 8]

/-- The new `a` and `b`, `(t + k m) / 2^64`, in place. -/
def updateAB : Prog isa := seqs [
  .block (fsetup aA aB ++ ptr .r7 aMz ++ ldW .r4 wIv ++ abFirst ++ cntN ++ [.subi .r8 .r8 1]),
  .ite (.zero .d .r8) (.block []) (countLoop .r8 abBody),
  .block abLast]

/-- The new `f`, `g`, `a` and `b`. -/
def update : Prog isa := seqs [.block spill, updateG, updateAB, .block restore]

/-- The count of the batches left decremented, its test in `r3`. -/
def countDown : List Instr := [.subi .r10 .r10 32768, .lsr .d .r3 .r10 15]

/-- A batch. -/
def batch : Prog isa := seqs [.block (start ++ wsteps 59 ++ save), update, .block countDown]

/-- The update of `f` and `g` alone, the borrowed registers saved around it. -/
def updateGS : Prog isa := seqs [.block spill, updateG, .block restore]

/-- A batch of `f` and `g` alone, for `gcd`. -/
def batchG : Prog isa := seqs [.block (start ++ wsteps 59 ++ save), updateGS, .block countDown]

/-! ## The start -/

/-- A Newton step of the inverse modulo powers of 2: `x := x (2 - m x)`, `m` in
`r5` and `x` in `r6`, through `r3` and `r4`. -/
def newton : List Instr := [.mul .r3 .r5 .r6, .li .r4 2, .sub .r3 .r4 .r3, .mul .r6 .r6 .r3]

/-- `init`'s first part: `r10 := n`; `[2] = m` with a zero word `ν`. -/
def initA : Prog isa := seqs [
  .seq (.block (ptr .r5 aMz ++ ptr .r6 aMin ++ [.addi .r10 .r11 0] ++ cntN)) (countLoop .r8 copyWBody),
  .block (topOf aMz ++ [.li .r0 0, .store .d .r0 .r6 0])]

/-- `init`'s second part: `-m⁻¹ mod 2^64` to the window, from `m`'s low word
`m₀`: `m₀` is its own inverse modulo `2^3` (an odd square is 1 modulo 8),
and five Newton steps make it right modulo `2^96`. -/
def initB : Prog isa :=
  .block (ptr .r4 aMz ++ [.load .d .r5 .r4 0, .addi .r6 .r5 0] ++ newton ++ newton ++ newton ++ newton ++
    newton ++ [.li .r3 0, .sub .r12 .r3 .r6] ++ ptr .r4 aW ++ [.store .d .r12 .r4 wIv])

/-- `init`'s third part: `f = m`, `g = x + m` if `x` is even, else `x`,
`(a, b) = (0, 1)`, `d = 1`, and `3 ν + 2` batches to run. -/
def initC : Prog isa := seqs [
  .seq (.block (ptr .r5 aF ++ ptr .r6 aMz ++ cntN1)) (countLoop .r8 copyWBody),
  .block (ptr .r5 aX ++ [.load .d .r11 .r5 0, .li .r0 1, .logic .and .r11 .r11 .r0, .logic .xor .r11 .r11 .r0]),
  mac aG aX aMz cntN,
  .block [.store .d .r9 .r5 0],
  .seq (.block (ptr .r5 aA ++ cntN1 ++ [.li .r0 0])) zerosW,
  .seq (.block (ptr .r5 aB ++ cntN1 ++ [.li .r0 0])) zerosW,
  .block (ptr .r5 aB ++ [.li .r0 1, .store .d .r0 .r5 0] ++ ptr .r5 aW ++ [.store .d .r0 .r5 wD] ++ cntN ++
    [.add .r3 .r8 .r8, .add .r3 .r3 .r8, .addi .r3 .r3 2, .lsl .r3 .r3 15, .add .r10 .r10 .r3])]

/-- The start: `[2] = m`, its word `ν` zero; `-m⁻¹ mod 2^64` to the window;
`f = m`, `g = x + m` if `x` is even, else `x`; `(a, b) = (0, 1)`, `d = 1`;
and `3 ν + 2` batches to run. -/
def init : Prog isa := seqs [initA, initB, initC]

/-! ## The end -/

/-- The mask of `[j]`'s sign (its word `ν`'s bit 63) into `r9`. -/
def signOf (j : Nat) : List Instr := topOf j ++ [.load .d .r9 .r6 0, .lsr .d .r9 .r9 63, .li .r0 0, .sub .r9 .r0 .r9]

/-- `[o] = [b]` if `[j] < 0`, else `[a]`, `ν + 1` words. -/
def signSel (j o a b : Nat) : Prog isa :=
  .seq (.block (signOf j ++ ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cntN1)) (countLoop .r8 selWBody)

/-- `a` from `(-m, 2m)` into `[0, m)`: `a + m` if `a < 0`, then less `m` if
that does not borrow. -/
def reduce : Prog isa := seqs [
  .block [.li .r11 1], mac aT3 aA aMz cntN1, signSel aA aA aA aT3, csub aA aA aT1]

/-- `a` into `[0, m)`, then `a := (m - a) mod m` if `f < 0`. -/
def normalize : Prog isa := seqs [reduce, subW aT3 aMz aA, signSel aF aA aA aT3, csub aA aA aT1]

/-- `a := 2 a mod m`. -/
def double : Prog isa := seqs [.block [.li .r11 1], mac aT3 aA aA cntN1, csub aA aT3 aT1]

/-- `5 (3 ν + 2)` doublings, counted in `r10` above `n`. -/
def doublings : Prog isa :=
  .seq (.block (cntN ++ [.lsl .r3 .r8 4, .sub .r3 .r3 .r8, .addi .r3 .r3 10, .lsl .r3 .r3 15, .add .r10 .r10 .r3]))
    (.loop (.seq double (.block countDown)) (.nonzero .d .r3))

/-- The digits from `r5` (`r8` of them) zeroed (`r0 = 0`). -/
def zeros : Prog isa := countLoop .r8 [.store .w .r0 .r5 0, .addi .r5 .r5 4]

/-- `[j]`'s `w + 2` digits zeroed. -/
def zeroW (j : Nat) : Prog isa := .seq (.block (ptr .r5 j ++ [.addi .r8 .r29 2, .li .r0 0])) zeros

/-- `[1] = |f|`. -/
def finishG : Prog isa := seqs [zeroW aGcd, subW aT1 aGcd aF, signSel aF aGcd aF aT1]

/-- `[3] = a`. -/
def finishY : Prog isa := seqs [
  zeroW aY, .seq (.block (ptr .r5 aY ++ ptr .r6 aA ++ cntN1)) (countLoop .r8 copyWBody)]

/-- `[1] = |f|` and `[3] = a`. -/
def finish : Prog isa := .seq finishG finishY

/-- `gcd(x, m)` alone into array 1, `n` in `r11`: the batches of `f` and `g`, and `|f|`. -/
def gcd : Prog isa := seqs [init, .loop batchG (.nonzero .d .r3), finishG]

/-- The inverse, `n` in `r11`. -/
def inverse : Prog isa := seqs [init, .loop batch (.nonzero .d .r3), normalize, doublings, finish]

/-- The inverse without its doublings: `[3] = y` with
`y 2^(5 (3 ν + 2)) x ≡ gcd(x, m) (mod m)`, for a caller that scales `y` itself. -/
def inverseS : Prog isa := seqs [init, .loop batch (.nonzero .d .r3), normalize, finish]

end VG.Impl.Rsa.PPC64LE.InvBatch
