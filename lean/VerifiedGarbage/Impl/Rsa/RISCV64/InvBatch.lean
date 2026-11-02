module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs

/-!
# The batched inverse modulo an odd number, on RISC-V

`inverse`: the inverse of `x` modulo an odd `m`, and `gcd(x, m)`, by batches
of 30 divsteps (Bernstein and Yang), as PPC64LE's
(`Impl/Rsa/PPC64LE/InvBatch.lean`), on numbers of `n` digits of 32 bits,
`n` read at run time (`s8`, at most twice the working space's `w` words), in
the key operations' arrays (`KeyWs.lean`), whose words are pairs of digits:
`x` in array 0 and `m` in array 8, both below `2^(32 n)`. Array 1 ends as
`gcd(x, m)` and array 3 as `y < m` with `y x ≡ gcd(x, m) (mod m)` (for
`m > 1`), `w` words each.

The state of `Proof/Divstep/Alg32Def.lean`'s `invRun 30`: `f` and `g` in
arrays 4 and 5, `n + 1` digits in two's complement; the coefficients `a`,
`b` in arrays 6 and 7, `n + 1` digits below `m`; `m` with a zero digit `n` in
array 2; `d`, the batch's matrix and `-m⁻¹ mod 2^32` in 64-bit words of
array 9 (the window, `w ≥ 4`).
Each batch runs 30 divsteps on the low digits of `f` and `g`
(`Proof/Divstep/WordDef.lean`'s `wstep`, unrolled, in `t0`–`t6`, `a4`, `a5`
and `a7`), then:

* `lin`: `[o] = u [a] + v [b]`, the top digit of each input signed, `n + 2`
  digits, the products in 64 bits (`|u|, |v| ≤ 2^30`) with a signed carry;
* `shr`: `[o] = [a] / 2^30`, `n + 1` digits, for the new `f` and `g`;
* `mred`: `[o] = (t + k m) / 2^32` reduced into `[0, m)` for the new `a`,
  `b`: `k = t₀ (-m⁻¹) mod 2^32` added (`mac`), the top digit fixed by the
  carry, `m` added (the result is then in `(0, 3m)`) and subtracted twice
  where it does not borrow (`csub`).

`n` stays in `s8` and the count of the batches left in `s7`, so every loop's
count and every address depends only on `w` and the base, all in
registers, and every choice is a masked selection. After `3 (n + 1)`
batches, `a` is negated if `f < 0` and doubled `6 (n + 1)` times modulo `m`
(each batch scaled it by `2^(30 - 32)`), and `|f|` is the gcd.
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

/-- The window's 64-bit words: `d`, the matrix `u v q r`, and `-m⁻¹ mod 2^32`. -/
def wD : Nat := 0
def wU : Nat := 8
def wV : Nat := 16
def wQ : Nat := 24
def wR : Nat := 32
def wIv : Nat := 40

/-- `t3 := n`. -/
def cntN : List Instr := [mov .t3 .s8]

/-- `t3 := n + 1`. -/
def cntN1 : List Instr := [.addi .t3 .s8 1]

/-- The window's word at `o` into `r`. -/
def ldW (r : Reg) (o : Nat) : List Instr := ptr r aW ++ [.load .d r r o]

/-! ## The digit loops -/

/-- One digit of `[a] - [b]`, the borrow in and out in `t4`, to `[o]`. -/
def subBody : List Instr :=
  [.load .w .t5 .t1 0, .load .w .t6 .t2 0, .sub .t5 .t5 .t6, .sub .t5 .t5 .t4,
    .store .w .t5 .t0 0, .shift .srl .d .t4 .t5 63, .addi .t0 .t0 4, .addi .t1 .t1 4,
    .addi .t2 .t2 4]

/-- One digit of `mask ? [b] : [a]`, the mask in `t4`, to `[o]`. -/
def selBody : List Instr :=
  [.load .w .t5 .t1 0, .load .w .t6 .t2 0, .logic .xor .t6 .t6 .t5, .logic .and .t6 .t6 .t4,
    .logic .xor .t6 .t6 .t5, .store .w .t6 .t0 0, .addi .t0 .t0 4, .addi .t1 .t1 4,
    .addi .t2 .t2 4]

/-- One digit of `[a]` to `[o]`. -/
def copyBody : List Instr :=
  [.load .w .t5 .t1 0, .store .w .t5 .t0 0, .addi .t0 .t0 4, .addi .t1 .t1 4]

/-- One digit of the comparison: `t4 |= [a] ^ [b]`. -/
def eqBody : List Instr :=
  [.load .w .t5 .t1 0, .load .w .t6 .t2 0, .logic .xor .t5 .t5 .t6, .logic .or .t4 .t4 .t5,
    .addi .t1 .t1 4, .addi .t2 .t2 4]

/-- The digits `[j]` (`t3` of them, from `t0`) zeroed. -/
def zeros : Prog isa := .seq (.block [.li .t5 0]) (countLoop .t3 [.store .w .t5 .t0 0, .addi .t0 .t0 4])

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

/-- The low digits of `f` and `g`, `d`, and the identity matrix. -/
def start : List Instr :=
  ptr .t0 aF ++ [.load .w .a4 .t0 0] ++ ptr .t0 aG ++ [.load .w .t0 .t0 0] ++ ldW .t6 wD ++
    [.li .t1 1, .li .t2 0, .li .t3 0, .li .t4 1]

/-- `d` and the matrix to the window. -/
def save : List Instr :=
  ptr .a4 aW ++ [.store .d .t6 .a4 wD, .store .d .t1 .a4 wU, .store .d .t2 .a4 wV,
    .store .d .t3 .a4 wQ, .store .d .t4 .a4 wR]

/-! ## The array operations -/

/-- One digit of `u [a] + v [b]` (`u`, `v` in `a5`, `a7`), the signed carry
in `t4`: the 64-bit sum's low digit to `[o]`, its arithmetic shift by 32
the carry. -/
def linBody : List Instr :=
  [.load .w .t5 .t1 0, .mul .t5 .a5 .t5, .load .w .t6 .t2 0, .mul .t6 .a7 .t6, .add .t5 .t5 .t6,
    .add .t5 .t5 .t4, .store .w .t5 .t0 0, .shift .sra .d .t4 .t5 32, .addi .t0 .t0 4,
    .addi .t1 .t1 4, .addi .t2 .t2 4]

/-- The top digit of `u [a] + v [b]`, each input's sign-extended (`addiw`),
and the carry after it, the sign. -/
def linTop : List Instr :=
  [.load .w .t5 .t1 0, .addiw .t5 .t5 0, .mul .t5 .a5 .t5,
    .load .w .t6 .t2 0, .addiw .t6 .t6 0, .mul .t6 .a7 .t6,
    .add .t5 .t5 .t6, .add .t5 .t5 .t4, .store .w .t5 .t0 0,
    .shift .sra .d .t4 .t5 32, .store .w .t4 .t0 4]

/-- `[o] = c₁ [a] + c₂ [b]`, the coefficients the window's words at `c₁` and
`c₂`: `n` digits, the top digit and the sign, `n + 2` digits. -/
def lin (c1 c2 o a b : Nat) : Prog isa := seqs [
  .block (ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ ldW .a5 c1 ++ ldW .a7 c2 ++ cntN ++ [.li .t4 0]),
  countLoop .t3 linBody, .block linTop]

/-- One digit of `[a] >> 30`: the digit's top two bits and the next's low 30. -/
def shrBody : List Instr :=
  [.load .w .t5 .t1 0, .load .w .t6 .t1 4, .shift .srl .d .t5 .t5 30, .shift .sll .d .t6 .t6 2,
    .add .t5 .t5 .t6, .store .w .t5 .t0 0, .addi .t0 .t0 4, .addi .t1 .t1 4]

/-- `[o] = [a] / 2^30`, `n + 1` digits from `n + 2`. -/
def shr (o a : Nat) : Prog isa :=
  .seq (.block (ptr .t0 o ++ ptr .t1 a ++ cntN1)) (countLoop .t3 shrBody)

/-- One digit of `[a] + k [b]` (`k < 2^32` in `a5`), the carry in `t4`: the
sum is below `2^64`. -/
def macBody : List Instr :=
  [.load .w .t5 .t2 0, .mul .t5 .a5 .t5, .load .w .t6 .t1 0, .add .t5 .t5 .t6, .add .t5 .t5 .t4,
    .store .w .t5 .t0 0, .shift .srl .d .t4 .t5 32, .addi .t0 .t0 4, .addi .t1 .t1 4,
    .addi .t2 .t2 4]

/-- The pointers of `[o] = [a] + k [b]`, the count `cnt` and no carry. -/
def macSetup (o a b : Nat) (cnt : List Instr) : List Instr :=
  ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ cnt ++ [.li .t4 0]

/-- `[o] = [a] + k [b]`, `cnt` digits, the carry out in `t4`. -/
def mac (o a b : Nat) (cnt : List Instr) : Prog isa := .seq (.block (macSetup o a b cnt)) (countLoop .t3 macBody)

/-- `[o] = [x] - m` where that does not borrow, else `[x]`, `n + 1` digits:
the difference into `[s]`, then selected by the borrow. -/
def csub (o x s : Nat) : Prog isa := seqs [
  .block (ptr .t0 s ++ ptr .t1 x ++ ptr .t2 aMz ++ cntN1 ++ [.li .t4 0]), countLoop .t3 subBody,
  .block (ptr .t0 o ++ ptr .t1 s ++ ptr .t2 x ++ cntN1 ++ [.li .t5 0, .sub .t4 .t5 .t4]),
  countLoop .t3 selBody]

/-- `[o] = (t + k m) / 2^32` into `[0, m)`, for `t = [t]` (`n + 2` digits,
signed), `k = t₀ (-m⁻¹) mod 2^32`. -/
def mred (t o : Nat) : Prog isa := seqs [
  .block (ptr .t0 t ++ ldW .t6 wIv ++ [.load .w .t5 .t0 0, .mul .a5 .t5 .t6, .shift .sll .d .a5 .a5 32,
    .shift .srl .d .a5 .a5 32]),
  mac t t aMz cntN1,
  .block [.load .w .t5 .t0 0, .add .t5 .t5 .t4, .store .w .t5 .t0 0],
  .block (ptr .t0 aT3 ++ ptr .t1 t ++ ptr .t2 aMz ++ [.addi .t1 .t1 4, .li .a5 1] ++ cntN1 ++ [.li .t4 0]),
  countLoop .t3 macBody,
  csub aT3 aT3 t, csub o aT3 t]

/-- The new `f` and `g`. -/
def updateG : Prog isa := seqs [lin wU wV aT1 aF aG, lin wQ wR aT2 aF aG, shr aF aT1, shr aG aT2]

/-- The new `a` and `b`. -/
def updateAB : Prog isa := seqs [lin wU wV aT1 aA aB, lin wQ wR aT2 aA aB, mred aT1 aA, mred aT2 aB]

/-- The new `f`, `g`, `a` and `b`. -/
def update : Prog isa := .seq updateG updateAB

/-- A batch, and the count of those left decremented. -/
def batch : Prog isa := seqs [.block (start ++ wsteps 30 ++ save), update, .block [.addi .s7 .s7 (-1)]]

/-- A batch of `f` and `g` alone. -/
def batchG : Prog isa := seqs [.block (start ++ wsteps 30 ++ save), updateG, .block [.addi .s7 .s7 (-1)]]

/-! ## The start -/

/-- Digit `n` of `[j]` := `v`. -/
def setTop (j v : Nat) : List Instr :=
  ptr .t1 j ++ [.shift .sll .d .t3 .s8 2, .add .t1 .t1 .t3, .li .t5 v, .store .w .t5 .t1 0]

/-- `init`'s first part: `[2] = m` with a zero digit `n`, `b = 1`, and `m`
replaced by 3 where it is 1. -/
def initA : Prog isa := seqs [
  .seq (.block (ptr .t0 aMz ++ ptr .t1 aMin ++ cntN)) (countLoop .t3 copyBody),
  .seq (.block (setTop aMz 0 ++ ptr .t0 aB ++ cntN1)) zeros,
  .seq (.block (ptr .t0 aB ++ [.li .t5 1, .store .w .t5 .t0 0] ++ ptr .t1 aMz ++ ptr .t2 aB ++ cntN1 ++
    [.li .t4 0])) (countLoop .t3 eqBody),
  .block ([.li .t5 0, .sub .t5 .t5 .t4, .shift .srl .d .t5 .t5 63, .logicImm .xor .t5 .t5 1,
    .shift .sll .d .t5 .t5 1] ++
    ptr .t0 aMz ++ [.load .w .t6 .t0 0, .logic .or .t6 .t6 .t5, .store .w .t6 .t0 0])]

/-- A Newton step of the inverse modulo powers of 2: `x := x (2 - m x)`, `m` in
`t5` and `x` in `t6`, through `a5` and `t4`. -/
def newton : List Instr := [.mul .a5 .t5 .t6, .li .t4 2, .sub .a5 .t4 .a5, .mul .t6 .t6 .a5]

/-- `init`'s second part: `-p⁻¹ mod 2^32` to the window, from `p`'s low digit
`p₀`: `p₀` is its own inverse modulo `2^3` (an odd square is 1 modulo 8),
and four Newton steps make it right modulo `2^48`. -/
def initB : Prog isa :=
  .block (ptr .a4 aMz ++ [.load .w .t5 .a4 0, mov .t6 .t5] ++ newton ++ newton ++ newton ++ newton ++
    [.li .a5 0, .sub .t1 .a5 .t6] ++ ptr .a4 aW ++ [.store .d .t1 .a4 wIv])

/-- `init`'s third part: `f = p`, `g = x + p` if `x` is even, else `x`, `a = 0`,
`d = 1`, and `3 (n + 1)` batches to run. -/
def initC : Prog isa := seqs [
  .seq (.block (ptr .t0 aF ++ ptr .t1 aMz ++ cntN1)) (countLoop .t3 copyBody),
  .block (ptr .t0 aX ++ [.load .w .a5 .t0 0, .logicImm .and .a5 .a5 1, .logicImm .xor .a5 .a5 1]),
  mac aG aX aMz cntN,
  .block [.store .w .t4 .t0 0],
  .seq (.block (ptr .t0 aA ++ cntN1)) zeros,
  .block (ptr .t0 aW ++ [.li .t5 1, .store .d .t5 .t0 wD,
    .addi .s7 .s8 1, .add .t5 .s7 .s7, .add .s7 .s7 .t5])]

/-- The start: `[2] = m`, its digit `n` zero; `b = 1`; `m` replaced by 3
where it is 1 (the modulus of the batches, `p`); `-p⁻¹ mod 2^32` to the
window; `f = p`, `g = x + p` if `x` is even, else `x`; `a = 0`, `d = 1`; and
`3 (n + 1)` batches to run. -/
def init : Prog isa := .seq initA (.seq initB initC)

/-! ## The end -/

/-- The mask of `f`'s sign (its digit `n`'s bit 31) into `t4`. -/
def signF : List Instr :=
  ptr .t1 aF ++ [.shift .sll .d .t3 .s8 2, .add .t1 .t1 .t3, .load .w .t4 .t1 0, .shift .srl .d .t4 .t4 31,
    .li .t5 0, .sub .t4 .t5 .t4]

/-- `[o] = [b]` if `f < 0`, else `[a]`, `n + 1` digits. -/
def signSel (o a b : Nat) : Prog isa :=
  .seq (.block (signF ++ ptr .t0 o ++ ptr .t1 a ++ ptr .t2 b ++ cntN1)) (countLoop .t3 selBody)

/-- `a := (m - a) mod m` if `f < 0`. -/
def normalize : Prog isa := seqs [
  .block (ptr .t0 aT3 ++ ptr .t1 aMz ++ ptr .t2 aA ++ cntN1 ++ [.li .t4 0]), countLoop .t3 subBody,
  signSel aA aA aT3, csub aA aA aT1]

/-- `a := 2 a mod m`. -/
def double : Prog isa := seqs [
  .block [.li .a5 1], mac aT3 aA aA cntN1, csub aA aT3 aT1]

/-- `6 (n + 1)` doublings, counted in `s7`. -/
def doublings : Prog isa :=
  .seq (.block [.addi .s7 .s8 1, .add .t5 .s7 .s7, .add .s7 .s7 .t5, .add .s7 .s7 .s7])
    (.loop (.seq double (.block [.addi .s7 .s7 (-1)])) (.nonzero .s7))

/-- `[j]`'s `w + 1` words (`2 w + 2` digits) zeroed. -/
def zeroW (j : Nat) : Prog isa := .seq (.block (ptr .t0 j ++ [.add .t3 .s9 .s9, .addi .t3 .t3 2])) zeros

/-- `[1] = |f|`. -/
def finishG : Prog isa := seqs [
  zeroW aGcd,
  .block (ptr .t0 aT1 ++ ptr .t1 aGcd ++ ptr .t2 aF ++ cntN1 ++ [.li .t4 0]), countLoop .t3 subBody,
  signSel aGcd aF aT1]

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

end VG.Impl.Rsa.RISCV64.InvBatch
