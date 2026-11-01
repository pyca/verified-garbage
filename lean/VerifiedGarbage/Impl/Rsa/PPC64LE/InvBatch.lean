module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-!
# The batched inverse modulo an odd number, on PPC64LE

`inverse`: the inverse of `x` modulo an odd `m`, and `gcd(x, m)`, by batches
of 30 divsteps (Bernstein and Yang), as i686's (`Impl/Rsa/X86/InvBatchRt.lean`),
on numbers of `n` digits of 32 bits, `n` read at run time (`r11` at entry), in
the key operations' arrays (`KeyWs.lean`): `x` in array 0 and `m` in array 8,
both below `2^(32 n)`, `n ≤ w`. Array 1 ends as `gcd(x, m)` and array 3 as
`y < m` with `y x ≡ gcd(x, m) (mod m)` (for `m > 1`), `w` digits each.

The state of `Proof/Divstep/Alg32Def.lean`'s `invRun 30`: `f` and `g` in
arrays 4 and 5, `n + 1` digits in two's complement; the coefficients `a`,
`b` in arrays 6 and 7, `n + 1` digits below `m`; `m` with a zero digit `n` in
array 2; `d`, the batch's matrix and `-m⁻¹ mod 2^32` (`minv`) in 64-bit
words of array 14 (the window). Each batch runs 30 divsteps on the low digits
of `f` and `g` (`Proof/Divstep/WordDef.lean`'s `wstep`, unrolled, in `r3`–`r9`
with `r0`, `r11`, `r12`), then:

* `lin`: `[o] = u [a] + v [b]`, the top digit of each input signed, `n + 2`
  digits, the products in 64 bits (`|u|, |v| ≤ 2^30`) with a signed carry;
* `shr`: `[o] = [a] / 2^30`, `n + 1` digits, for the new `f` and `g`;
* `mred`: `[o] = (t + k m) / 2^32` reduced into `[0, m)` for the new `a`,
  `b`: `k = t₀ (-m⁻¹) mod 2^32` added (`mac`), the top digit fixed by the
  carry, `m` added (the result is then in `(0, 3m)`) and subtracted twice
  where it does not borrow (`csub`).

`n` and the count of the batches left share `r10`: `n` in its low 15 bits, the
count above. So every loop's count and every address depends only on `n`,
`w` and the base, all in registers, and every choice is a masked selection.
After `3 (n + 1)` batches, `a` is negated if `f < 0` and doubled `6 (n + 1)`
times modulo `m` (each batch scaled it by `2^(30 - 32)`), and `|f|` is the gcd.
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

/-- The window's 64-bit words: `d`, the matrix `u v q r`, and `-m⁻¹ mod 2^32`. -/
def wD : Nat := 0
def wU : Nat := 8
def wV : Nat := 16
def wQ : Nat := 24
def wR : Nat := 32
def wIv : Nat := 40

/-- `r8 := n`, the low 15 bits of `r10`. -/
def cntN : List Instr := [.lsl .r8 .r10 49, .lsr .d .r8 .r8 49]

/-- `r8 := n + 1`. -/
def cntN1 : List Instr := cntN ++ [.addi .r8 .r8 1]

/-- The window's word at `o` into `r`. -/
def ldW (r : Reg) (o : Nat) : List Instr := ptr r aW ++ [.load .d r r o]

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

/-- The low digits of `f` and `g`, `d`, and the identity matrix. -/
def start : List Instr :=
  ptr .r5 aF ++ [.load .w .r4 .r5 0] ++ ptr .r5 aG ++ [.load .w .r5 .r5 0] ++ ldW .r3 wD ++
    [.li .r6 1, .li .r7 0, .li .r8 0, .li .r9 1]

/-- `d` and the matrix to the window. -/
def save : List Instr :=
  ptr .r4 aW ++ [.store .d .r3 .r4 wD, .store .d .r6 .r4 wU, .store .d .r7 .r4 wV,
    .store .d .r8 .r4 wQ, .store .d .r9 .r4 wR]

/-! ## The array operations -/

/-- One digit of `u [a] + v [b]` (`u`, `v` in `r11`, `r12`), the signed carry
in `r9`: the 64-bit sum's low digit to `[o]`, its arithmetic shift by 32
(the logical one less `2^32` where it is negative) the carry. -/
def linBody : List Instr :=
  [.load .w .r0 .r6 0, .mul .r0 .r11 .r0, .load .w .r3 .r7 0, .mul .r3 .r12 .r3, .add .r0 .r0 .r3,
    .add .r0 .r0 .r9, .store .w .r0 .r5 0, .lsr .d .r9 .r0 32, .lsr .d .r3 .r0 63, .lsl .r3 .r3 32,
    .sub .r9 .r9 .r3, .addi .r5 .r5 4, .addi .r6 .r6 4, .addi .r7 .r7 4]

/-- The top digit of `u [a] + v [b]`, each input's sign-extended (less `2^32`
where its bit 31 is set, through `r4`), and the carry after it, the sign. -/
def linTop : List Instr :=
  [.load .w .r0 .r6 0, .lsr .d .r4 .r0 31, .lsl .r4 .r4 32, .sub .r0 .r0 .r4, .mul .r0 .r11 .r0,
    .load .w .r3 .r7 0, .lsr .d .r4 .r3 31, .lsl .r4 .r4 32, .sub .r3 .r3 .r4, .mul .r3 .r12 .r3,
    .add .r0 .r0 .r3, .add .r0 .r0 .r9, .store .w .r0 .r5 0,
    .lsr .d .r9 .r0 32, .lsr .d .r3 .r0 63, .lsl .r3 .r3 32, .sub .r9 .r9 .r3, .store .w .r9 .r5 4]

/-- `[o] = c₁ [a] + c₂ [b]`, the coefficients the window's words at `c₁` and
`c₂`: `n` digits, the top digit and the sign, `n + 2` digits. -/
def lin (c1 c2 o a b : Nat) : Prog isa := seqs [
  .block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ ldW .r11 c1 ++ ldW .r12 c2 ++ cntN ++ [.li .r9 0]),
  countLoop .r8 linBody, .block linTop]

/-- One digit of `[a] >> 30`: the digit's top two bits and the next's low 30. -/
def shrBody : List Instr :=
  [.load .w .r0 .r6 0, .load .w .r3 .r6 4, .lsr .d .r0 .r0 30, .lsl .r3 .r3 2, .add .r0 .r0 .r3,
    .store .w .r0 .r5 0, .addi .r5 .r5 4, .addi .r6 .r6 4]

/-- `[o] = [a] / 2^30`, `n + 1` digits from `n + 2`. -/
def shr (o a : Nat) : Prog isa :=
  .seq (.block (ptr .r5 o ++ ptr .r6 a ++ cntN1)) (countLoop .r8 shrBody)

/-- One digit of `[a] + k [b]` (`k < 2^32` in `r11`), the carry in `r9`: the
sum is below `2^64`. -/
def macBody : List Instr :=
  [.load .w .r0 .r7 0, .mul .r0 .r11 .r0, .load .w .r3 .r6 0, .add .r0 .r0 .r3, .add .r0 .r0 .r9,
    .store .w .r0 .r5 0, .lsr .d .r9 .r0 32, .addi .r5 .r5 4, .addi .r6 .r6 4, .addi .r7 .r7 4]

/-- The pointers of `[o] = [a] + k [b]`, the count `cnt` and no carry. -/
def macSetup (o a b : Nat) (cnt : List Instr) : List Instr :=
  ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cnt ++ [.li .r9 0]

/-- `[o] = [a] + k [b]`, `cnt` digits, the carry out in `r9`. -/
def mac (o a b : Nat) (cnt : List Instr) : Prog isa := .seq (.block (macSetup o a b cnt)) (countLoop .r8 macBody)

/-- `[o] = [x] - m` where that does not borrow, else `[x]`, `n + 1` digits:
the difference into `[s]`, then selected by the borrow. -/
def csub (o x s : Nat) : Prog isa := seqs [
  .block (ptr .r5 s ++ ptr .r6 x ++ ptr .r7 aMz ++ cntN1 ++ [.li .r9 0]), countLoop .r8 subBody,
  .block (ptr .r5 o ++ ptr .r6 s ++ ptr .r7 x ++ cntN1 ++ [.li .r0 0, .sub .r9 .r0 .r9]),
  countLoop .r8 selBody]

/-- `[o] = (t + k m) / 2^32` into `[0, m)`, for `t = [t]` (`n + 2` digits,
signed), `k = t₀ (-m⁻¹) mod 2^32`. -/
def mred (t o : Nat) : Prog isa := seqs [
  .block (ptr .r5 t ++ ldW .r3 wIv ++ [.load .w .r0 .r5 0, .mul .r11 .r0 .r3, .lsr .w .r11 .r11 0]),
  mac t t aMz cntN1,
  .block [.load .w .r0 .r5 0, .add .r0 .r0 .r9, .store .w .r0 .r5 0],
  .block (ptr .r5 aT3 ++ ptr .r6 t ++ ptr .r7 aMz ++ [.addi .r6 .r6 4, .li .r11 1] ++ cntN1 ++ [.li .r9 0]),
  countLoop .r8 macBody,
  csub aT3 aT3 t, csub o aT3 t]

/-- The new `f`, `g`, `a` and `b`. -/
def update : Prog isa := seqs [
  lin wU wV aT1 aF aG, lin wQ wR aT2 aF aG, shr aF aT1, shr aG aT2,
  lin wU wV aT1 aA aB, lin wQ wR aT2 aA aB, mred aT1 aA, mred aT2 aB]

/-- A batch, and the count of those left decremented, its test in `r3`. -/
def batch : Prog isa := seqs [
  .block (start ++ wsteps 30 ++ save), update, .block [.subi .r10 .r10 32768, .lsr .d .r3 .r10 15]]

/-! ## The start -/

/-- The digits `[j]` (`r8` of them, from `r5`) zeroed. -/
def zeros : Prog isa := countLoop .r8 [.store .w .r0 .r5 0, .addi .r5 .r5 4]

/-- `[2] = m`, its digit `n` zero, `r10 := n`; `b = 1`; `m` replaced by 3 where
it is 1 (the modulus of the batches, `p`); `-p⁻¹ mod 2^32` to the window;
`f = p`, `g = x + p` if `x` is even, else `x`; `a = 0`, `d = 1`; and
`3 (n + 1)` batches to run. -/
def init : Prog isa := seqs [
  .block (ptr .r5 aMz ++ ptr .r6 aMin ++ [.addi .r10 .r11 0] ++ cntN), countLoop .r8 copyBody,
  .block ([.li .r0 0, .store .w .r0 .r5 0] ++ ptr .r5 aB ++ cntN1), zeros,
  .block (ptr .r5 aB ++ [.li .r0 1, .store .w .r0 .r5 0] ++ ptr .r6 aMz ++ ptr .r7 aB ++ cntN1 ++ [.li .r9 0]),
  countLoop .r8 eqBody,
  .block ([.li .r0 0, .sub .r0 .r0 .r9, .lsr .d .r0 .r0 63, .li .r3 1, .logic .xor .r0 .r0 .r3, .lsl .r0 .r0 1] ++
    ptr .r5 aMz ++ [.load .w .r3 .r5 0, .logic .or .r3 .r3 .r0, .store .w .r3 .r5 0] ++
    ptr .r10 aMz ++ VG.Impl.Bignum.PPC64LE.PublicChecked.minv ++ ptr .r5 aW ++
    [.store .d .r12 .r5 wIv, .addi .r10 .r11 0] ++ ptr .r5 aF ++ ptr .r6 aMz ++ cntN1),
  countLoop .r8 copyBody,
  .block (ptr .r5 aX ++ [.load .w .r11 .r5 0, .lsl .r11 .r11 63, .lsr .d .r11 .r11 63, .li .r0 1,
    .logic .xor .r11 .r11 .r0]),
  mac aG aX aMz cntN,
  .block ([.store .w .r9 .r5 0] ++ ptr .r5 aA ++ cntN1 ++ [.li .r0 0]), zeros,
  .block (ptr .r5 aW ++ [.li .r0 1, .store .d .r0 .r5 wD,
    .addi .r3 .r10 1, .add .r0 .r3 .r3, .add .r3 .r3 .r0, .lsl .r3 .r3 15, .add .r10 .r10 .r3])]

/-! ## The end -/

/-- The mask of `f`'s sign (its digit `n`'s bit 31) into `r9`. -/
def signF : List Instr :=
  ptr .r6 aF ++ cntN ++ [.lsl .r8 .r8 2, .add .r6 .r6 .r8, .load .w .r9 .r6 0, .lsr .d .r9 .r9 31, .li .r0 0,
    .sub .r9 .r0 .r9]

/-- `[o] = [b]` if `f < 0`, else `[a]`, `n + 1` digits. -/
def signSel (o a b : Nat) : Prog isa :=
  .seq (.block (signF ++ ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cntN1)) (countLoop .r8 selBody)

/-- `a := (m - a) mod m` if `f < 0`. -/
def normalize : Prog isa := seqs [
  .block (ptr .r5 aT3 ++ ptr .r6 aMz ++ ptr .r7 aA ++ cntN1 ++ [.li .r9 0]), countLoop .r8 subBody,
  signSel aA aA aT3, csub aA aA aT1]

/-- `a := 2 a mod m`. -/
def double : Prog isa := seqs [
  .block [.li .r11 1], mac aT3 aA aA cntN1, csub aA aT3 aT1]

/-- `6 (n + 1)` doublings, counted in `r10` above `n`. -/
def doublings : Prog isa :=
  .seq (.block [.addi .r3 .r10 1, .add .r0 .r3 .r3, .add .r3 .r3 .r0, .add .r3 .r3 .r3, .lsl .r3 .r3 15,
      .add .r10 .r10 .r3])
    (.loop (.seq double (.block [.subi .r10 .r10 32768, .lsr .d .r3 .r10 15])) (.nonzero .d .r3))

/-- `[j]`'s `w + 1` digits zeroed. -/
def zeroW (j : Nat) : Prog isa := .seq (.block (ptr .r5 j ++ [.addi .r8 .r29 1, .li .r0 0])) zeros

/-- `[1] = |f|` and `[3] = a`, `w` digits each. -/
def finish : Prog isa := seqs [
  zeroW aGcd,
  .block (ptr .r5 aT1 ++ ptr .r6 aGcd ++ ptr .r7 aF ++ cntN1 ++ [.li .r9 0]), countLoop .r8 subBody,
  signSel aGcd aF aT1,
  zeroW aY,
  .block (ptr .r5 aY ++ ptr .r6 aA ++ cntN1), countLoop .r8 copyBody]

/-- The inverse, `n` in `r11`. -/
def inverse : Prog isa := seqs [init, .loop batch (.nonzero .d .r3), normalize, doublings, finish]

end VG.Impl.Rsa.PPC64LE.InvBatch
