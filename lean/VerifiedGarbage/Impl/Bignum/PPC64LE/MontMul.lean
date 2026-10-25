module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Bignum.Layout

/-!
# Montgomery multiplication on PPC64LE

`vg_rsa_mont_mul(ws = r3, ws_len = r4, o = r5, a = r6, b = r7)` in the
working space of `Impl/Bignum/Layout.lean`: a header of 32 words, then eight
arrays of `w + 2` words, the modulus `m` in array 0, the accumulator in
array 2 and a temporary in array 3.

The multiplication is coarsely integrated operand scanning (CIOS) in radix
`2⁶⁴`, with the carries through `XER`'s CA (`addc`, `addze`). The
accumulator `T` is `w + 1` words between rounds, and `w + 2` within one: for
each word `aᵢ` of `a`,

* one pass computes `T := T + aᵢ b`: for each word `bⱼ`, the 128-bit `tⱼ +
  aᵢ bⱼ + c` (which fits: `(2⁶⁴ - 1)² + 2 (2⁶⁴ - 1) = 2¹²⁸ - 1`), its low
  word stored as `tⱼ` and its high word the next carry `c`; then `t_w + c`
  into word `w` and its carry into word `w + 1`;
* `u = t₀ (-m⁻¹) mod 2⁶⁴`, so that `T + u m` is a multiple of `2⁶⁴`;
* a second pass computes `T := (T + u m) / 2⁶⁴` the same way, each word
  stored one word down, and words `w`, `w + 1` plus the carry stored at `w -
  1`, `w`.

`-m⁻¹ mod 2⁶⁴` is computed from the header's `-m⁻¹ mod 2³²` (`y`) by one
step of Newton's iteration, `y (2 + m₀ y) mod 2⁶⁴`, since `m₀ y (2 + m₀ y)
+ 1 = (m₀ y + 1)²`.

After the `w` rounds, `T < 2 m` and `T 2^(64 w) ≡ a b (mod m)`. Then, on the
numbers as `n = 2 w` 32-bit digits (the words are little-endian), `T - m` is
computed into the temporary, digit by digit with the borrow in the sign bit
of a 64-bit difference, and the borrow out of the top digit selects `T` or
`T - m` with a mask.

Every loop counts a register down from a public count (`w`, `w - 1`, `n`),
every address is a pointer plus a constant, and the pointers are the
header's (loaded once, at the start, before any store) advanced by 8 per
word (4 per digit), so only the pointers and `w` affect timing.

The code takes a scratch buffer (`r8`, 72 bytes) where it saves the
nonvolatile `r14`–`r22`, keeping its address in `r21`.

Registers: `r5` `o`'s base, `r6` (advancing over) `a`, `r7` `b`'s base, `r8`
the accumulator's, `r9` the temporary's, `r10` `m`'s, `r11` `n`, `r12`
`-m⁻¹ mod 2³²`; in the rounds, `r0` `-m⁻¹ mod 2⁶⁴`, `r3` `w`, `r4` the
rounds left, `r14` the pointer into the accumulator, `r15` into `b` or `m`,
`r16` the words left, `r17` `aᵢ` or `u`, `r18` the carry, `r19`, `r20` a
product's low and high words, `r22` a word of the accumulator; in the
final subtraction, `r14`–`r16` the pointers, `r17` the digits left, `r20`
the borrow and the mask, and `r0`, `r3` temporaries.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE

open VG.PPC64LE VG.Impl.Bignum

/-! ## Saving and restoring the nonvolatile registers -/

/-- The nonvolatile registers used, in the order they are saved: `r21` keeps
the scratch buffer's address. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r21].getD i .r14

/-- Save them in the scratch buffer at `r8`, and keep its address in `r21`. -/
def save : List Instr :=
  (List.range 9).flatMap (fun i => [.store .d (saved i) .r8 (8 * i)]) ++ [.addi .r21 .r8 0]

/-- Restore them, through `r21`, which is restored last. -/
def restore : List Instr :=
  (List.range 8).flatMap (fun i => [.load .d (saved i) .r21 (8 * i)]) ++ [.load .d .r21 .r21 64]

/-! ## The arguments -/

/-- The address of the header word of the array whose index is in the low
half of `r`, less 64, into `r`. -/
def slotOf (r : Reg) : List Instr := [.lsr .w r r 0, .lsl r r 3, .add r .r3 r]

/-- The indices of `o`, `a` and `b` into addresses in the header. -/
def args : List Instr := slotOf .r5 ++ slotOf .r6 ++ slotOf .r7

/-- The bases, `n = 2 w`, `-m⁻¹ mod 2³²` (the low half of the header's
word) and the rounds' count, from the header. -/
def loads : List Instr :=
  [.load .d .r5 .r5 64, .load .d .r6 .r6 64, .load .d .r7 .r7 64,
    .load .d .r8 .r3 (8 * sArr 2), .load .d .r9 .r3 (8 * sArr 3), .load .d .r10 .r3 (8 * sArr 0),
    .load .d .r11 .r3 (8 * sW), .lsl .r11 .r11 1, .load .w .r12 .r3 (8 * sMinv), .addi .r4 .r11 0]

def bases : List Instr := args ++ loads

/-! ## Loops -/

/-- `do body; cnt -= 1 while cnt ≠ 0`, for `cnt` at least 1. -/
def countLoop (cnt : Reg) (body : List Instr) : Prog isa :=
  .loop (.block (body ++ ([.subi cnt cnt 1] : List Instr))) (.nonzero .d cnt)

/-- The start of the arithmetic: `-m⁻¹ mod 2⁶⁴` into `r0`, from `m₀` and `r12 =
-m⁻¹ mod 2³²` (`y`): `y (2 + m₀ y)`; `w` into `r3` and the rounds' count `r4`;
then the accumulator's first `w + 1` words (its digits `0` to `n + 1`) := 0. -/
def zeroAcc : Prog isa :=
  .seq (.block [.load .d .r3 .r10 0, .mul .r3 .r3 .r12, .addi .r3 .r3 2, .mul .r0 .r3 .r12,
      .lsr .d .r3 .r11 1, .addi .r4 .r3 0, .addi .r14 .r8 0, .addi .r17 .r3 1, .li .r22 0])
    (countLoop .r17 [.store .d .r22 .r14 0, .addi .r14 .r14 8])

/-! ## A round -/

/-- A multiply-accumulate step, the accumulator's pointer `r14` at word `j`
and `r15` at word `j` of `b` or `m` (`k = 0`), or both one word below (`k =
8`): `x = tⱼ + r17 · sⱼ + c` (the words at `r14 + k` and `r15 + k`, the carry
`r18`), its low word stored at `r14` and its high word into `r18`, and the
pointers advanced. -/
def montMac (k : Nat) : List Instr :=
  [.load .d .r19 .r15 k, .mulhu .r20 .r17 .r19, .mul .r19 .r17 .r19, .addc .r19 .r19 .r18,
    .addze .r20 .r20, .load .d .r22 .r14 k, .addc .r22 .r22 .r19, .addze .r18 .r20,
    .store .d .r22 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8]

/-- `aᵢ` into `r17`, the pointers at word 0, `w` words left and the carry 0. -/
def montMulHead : List Instr :=
  [.load .d .r17 .r6 0, .addi .r6 .r6 8, .addi .r14 .r8 0, .addi .r15 .r7 0, .addi .r16 .r3 0,
    .li .r18 0]

/-- Word `w` (at `r14`) `+= c`, and its carry into word `w + 1`. -/
def montMulTop : List Instr :=
  [.load .d .r22 .r14 0, .addc .r22 .r22 .r18, .store .d .r22 .r14 0, .li .r22 0, .addze .r22 .r22,
    .store .d .r22 .r14 8]

/-- `T := T + aᵢ b`. -/
def montMulPass : Prog isa :=
  .seq (.block montMulHead) (.seq (countLoop .r16 (montMac 0)) (.block montMulTop))

/-- `u = t₀ (-m⁻¹) mod 2⁶⁴` into `r17`, the carry of `t₀ + u m₀` (whose low
word is 0) into `r18`, the pointers at word 0 and `w - 1` words left. -/
def montRedHead : List Instr :=
  [.load .d .r22 .r8 0, .mul .r17 .r22 .r0, .load .d .r19 .r10 0, .mulhu .r20 .r17 .r19,
    .mul .r19 .r17 .r19, .addc .r19 .r19 .r22, .addze .r18 .r20, .addi .r14 .r8 0, .addi .r15 .r10 0,
    .subi .r16 .r3 1]

/-- Words `w` and `w + 1` (above `r14`, at word `w - 1`) plus the carry,
stored one word down. -/
def montRedTop : List Instr :=
  [.load .d .r22 .r14 8, .addc .r22 .r22 .r18, .store .d .r22 .r14 0, .load .d .r22 .r14 16,
    .addze .r22 .r22, .store .d .r22 .r14 8]

/-- `T := (T + u m) / 2⁶⁴`. -/
def montRedPass : Prog isa :=
  .seq (.block montRedHead) (.seq (countLoop .r16 (montMac 8)) (.block montRedTop))

/-- One round: `T := (T + aᵢ b + u m) / 2⁶⁴`. -/
def round : Prog isa := .seq montMulPass montRedPass

/-- The `w` rounds, counted by `r4`. -/
def rounds : Prog isa :=
  .loop (.seq round (.block [.subi .r4 .r4 1])) (.nonzero .d .r4)

/-! ## The final subtraction -/

/-- `[tmp] = T - m` over `n` digits, the borrow in `r20` (the sign bit of each
difference), then `r20` := all ones if `T < m` (the top digit `tₙ` minus the
borrow is negative), else 0. -/
def subMod : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r10 0, .addi .r17 .r11 0,
      .li .r20 0])
    (.seq (countLoop .r17 [.load .w .r0 .r14 0, .load .w .r3 .r16 0, .sub .r0 .r0 .r3,
        .sub .r0 .r0 .r20, .store .w .r0 .r15 0, .lsr .d .r20 .r0 63, .addi .r14 .r14 4,
        .addi .r15 .r15 4, .addi .r16 .r16 4])
      (.block [.load .w .r0 .r14 0, .sub .r0 .r0 .r20, .lsr .d .r0 .r0 63, .li .r3 0,
        .sub .r20 .r3 .r0]))

/-- `[o] = mask ? T : [tmp]`, digit by digit, the mask in `r20`. -/
def selectAcc : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r5 0, .addi .r17 .r11 0])
    (countLoop .r17 [.load .w .r0 .r15 0, .load .w .r3 .r14 0, .logic .xor .r3 .r3 .r0,
      .logic .and .r3 .r3 .r20, .logic .xor .r3 .r3 .r0, .store .w .r3 .r16 0,
      .addi .r14 .r14 4, .addi .r15 .r15 4, .addi .r16 .r16 4])

/-- The arithmetic, after the bases are loaded. -/
def tail : Prog isa := .seq zeroAcc (.seq rounds (.seq subMod selectAcc))

/-- `vg_rsa_mont_mul(ws, ws_len, o, a, b, scratch)`: `[o] = [a] [b] R⁻¹ mod m`
for `R = 2^(64 w)`. -/
def mul : Prog isa :=
  .seq (.block save) (.seq (.seq (.block args) (.seq (.block loads) tail)) (.block restore))

end VG.Impl.Bignum.PPC64LE
