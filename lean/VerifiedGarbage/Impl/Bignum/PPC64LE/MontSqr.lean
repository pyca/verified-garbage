module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul

/-!
# Montgomery squaring on PPC64LE

`sqrTail`: `[o] = [a]² R⁻¹ mod m` for `R = 2^(64 w)`, in `vg_rsa_mont_mul`'s
working space and with `tail`'s registers (`r5` `o`'s base, `r6` `a`'s, `r8`
the accumulator's, `r9` the temporary's, `r10` `m`'s, `r11` `n = 2 w`, `r12`
`-m⁻¹ mod 2³²`), so that it can replace `tail` where `a = b`. It writes only
`tail`'s registers and arrays (2, 3 and `o`).

It is `tail`'s FIOS with the products `aᵢ aⱼ` for `j < i` left out: round
`i` adds `aᵢ Bᵢ` and `u m` to `T`, for

  `Bᵢ = aᵢ 2^(64 i) + 2 Σ_(j > i) aⱼ 2^(64 j)`, so that `Σᵢ aᵢ Bᵢ 2^(64 i) = a²`.

`Bᵢ` is kept in array 3 (`b`), `w + 1` words: first `D = 2 a` (`dbl`), then
each round sets word `i` to `aᵢ` and takes the bit `aᵢ` shifted into word
`i + 1` back out of it (`prep`); words above `i + 1` are `D`'s, and words below
`i` are not read. Round `i`'s words `j < i` add `u mⱼ` alone (`rstep`), and
words `j ≥ i` add `aᵢ bⱼ + u mⱼ` (`fiosStep`); word `w` adds `aᵢ b_w`, `b_w`
being 0 or 1, to `t_w` and both carries (`top`). Each round divides by `2⁶⁴`
as in `tail`, so after the `w` rounds `T < 2 m` (for `a < m`: `a² < m R`) and
`T R ≡ a²`; then `tail`'s final subtraction and selection.

Every loop counts a register down from a public count (`w`, `w - i`, `i - 1`,
and those modulo and divided by 4, from `n = 2 w` and the rounds left `r4`),
and every address is a pointer plus a constant.

Registers, besides `tail`'s: `r4` the rounds left `w - i`; in `prep`, `r19`
at `b`'s word `i`.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE.MontSqr

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE

/-- `b := D = 2 a`, `w + 1` words: `D_j = 2 aⱼ mod 2⁶⁴` plus the top bit of
`a_(j - 1)`, and `D_w` the top bit of `a_(w - 1)`. -/
def dbl : Prog isa :=
  .seq (.block [.addi .r14 .r6 0, .addi .r15 .r9 0, .li .r20 0, .lsr .d .r16 .r11 1])
    (.seq (countLoop .r16 [.load .d .r19 .r14 0, .lsl .r22 .r19 1, .add .r22 .r22 .r20, .lsr .d .r20 .r19 63,
        .store .d .r22 .r15 0, .addi .r14 .r14 8, .addi .r15 .r15 8])
      (.block [.store .d .r20 .r15 0]))

/-- Round `i`'s `b` (`r4 = w - i`, `r6` at `aᵢ`, advanced): `aᵢ` into `r17` and
`b`'s word `i`, and `b`'s word `i + 1` less `aᵢ`'s top bit. -/
def prep : List Instr :=
  [.load .d .r17 .r6 0, .addi .r6 .r6 8, .lsl .r19 .r11 2, .add .r19 .r19 .r9, .lsl .r20 .r4 3,
    .sub .r19 .r19 .r20, .store .d .r17 .r19 0, .load .d .r20 .r19 8, .lsr .d .r22 .r17 63, .sub .r20 .r20 .r22,
    .store .d .r20 .r19 8]

/-- Round 0's word 0: `fiosHead` with `b` from array 3. -/
def head0 : List Instr :=
  [.load .d .r19 .r9 0, .load .d .r20 .r8 0,
    .mul .r18 .r17 .r19, .mulhu .r19 .r17 .r19, .addc .r20 .r20 .r18, .addze .r18 .r19,
    .load .d .r3 .r10 0, .mul .r22 .r3 .r12, .addi .r22 .r22 2, .mul .r22 .r22 .r12, .mul .r0 .r20 .r22,
    .mul .r22 .r0 .r3, .mulhu .r19 .r0 .r3, .addc .r22 .r22 .r20, .addze .r22 .r19,
    .addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r3 .r10 0]

/-- A later round's word 0, without `aᵢ`'s product: `u = t₀ (-m⁻¹) mod 2⁶⁴`
into `r0` and the second carry `d = (t₀ + u m₀) / 2⁶⁴` into `r22`; the
pointers at word 0. -/
def headR : List Instr :=
  [.load .d .r20 .r8 0, .load .d .r3 .r10 0, .mul .r22 .r3 .r12, .addi .r22 .r22 2, .mul .r22 .r22 .r12,
    .mul .r0 .r20 .r22, .mul .r22 .r0 .r3, .mulhu .r19 .r0 .r3, .addc .r22 .r22 .r20, .addze .r22 .r19,
    .addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r3 .r10 0]

/-- Word `j < i` of a round, the pointers at word `j - 1` less `k`: `y = tⱼ +
u mⱼ + d`, `d` := its high word and its low word stored at `r14 + k`. -/
def rstep (k : Nat) : List Instr :=
  [.load .d .r19 .r3 (k + 8), .mul .r20 .r0 .r19, .mulhu .r19 .r0 .r19, .load .d .r18 .r14 (k + 8),
    .addc .r20 .r20 .r18, .addze .r19 .r19, .addc .r20 .r20 .r22, .addze .r22 .r19, .store .d .r20 .r14 k]

/-- `U` of those words, and the pointers advanced past them. -/
def rgroup (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => rstep (8 * k)) ++
    [.addi .r14 .r14 (8 * U), .addi .r15 .r15 (8 * U), .addi .r3 .r3 (8 * U)]

/-- Word `w` plus both carries and `aᵢ b_w`, stored at words `w - 1` and `w`. -/
def top : List Instr :=
  [.lsl .r20 .r11 2, .add .r20 .r20 .r9, .load .d .r20 .r20 0, .mul .r20 .r17 .r20,
    .load .d .r19 .r14 8, .addc .r18 .r18 .r19, .li .r19 0, .addze .r19 .r19, .addc .r18 .r18 .r22,
    .addze .r19 .r19, .addc .r18 .r18 .r20, .addze .r19 .r19, .store .d .r18 .r14 0, .store .d .r19 .r14 8]

/-- `r16 :=` `(i - 1) mod 4` and `(i - 1) / 4`, for `i = w - r4`. -/
def rRem : List Instr :=
  [.lsr .d .r16 .r11 1, .subi .r16 .r16 1, .sub .r16 .r16 .r4, .lsl .r16 .r16 62, .lsr .d .r16 .r16 62]
def rQuot : List Instr := [.lsr .d .r16 .r11 1, .subi .r16 .r16 1, .sub .r16 .r16 .r4, .lsr .d .r16 .r16 2]

/-- `r16 :=` `(w - i) mod 4` and `(w - i) / 4`. -/
def fRem : List Instr := [.lsl .r16 .r4 62, .lsr .d .r16 .r16 62]
def fQuot : List Instr := [.lsr .d .r16 .r4 2]

/-- Round 0: `tail`'s `round` with `b` from array 3 and the top word's
product. -/
def round0 : Prog isa :=
  .seq (.block (prep ++ head0 ++ fiosRem)) (.seq (countLoop? (fiosGroup 1)) (.seq (.block fiosQuot)
    (.seq (countLoop? (fiosGroup unroll)) (.block (top ++ [.subi .r4 .r4 1])))))

/-- Round `i ≥ 1`: words `1` to `i - 1` with `u mⱼ` alone, then words `i` to
`w - 1` as in `tail`, one at a time then four at a time. -/
def roundI : Prog isa :=
  .seq (.block (prep ++ headR ++ rRem)) (.seq (countLoop? (rgroup 1)) (.seq (.block rQuot)
    (.seq (countLoop? (rgroup unroll)) (.seq (.block (.li .r18 0 :: fRem)) (.seq (countLoop? (fiosGroup 1))
    (.seq (.block fQuot) (.seq (countLoop? (fiosGroup unroll)) (.block (top ++ [.subi .r4 .r4 1])))))))))

/-- `[o] = [a]² R⁻¹ mod m`, after `tail`'s bases are loaded. -/
def sqrTail : Prog isa :=
  .seq zeroAcc (.seq dbl (.seq round0 (.seq (.loop roundI (.nonzero .d .r4)) (.seq subMod64 selectAcc64))))

end VG.Impl.Bignum.PPC64LE.MontSqr
