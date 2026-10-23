module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Bignum.Layout

/-!
# Montgomery multiplication on PPC64LE

`vg_rsa_mont_mul(ws = r3, ws_len = r4, o = r5, a = r6, b = r7)` in the
working space of `Impl/Bignum/Layout.lean`: a header of 32 words, then eight
arrays of `w + 2` words, the modulus `m` in array 0, the accumulator in
array 2 and a temporary in array 3.

The model has no carry bit, so the numbers are read as `n = 2 w` 32-bit
digits (the words are little-endian), and every product of two digits plus
two more digits fits in 64 bits: `(2³² - 1)² + 2 (2³² - 1) = 2⁶⁴ - 1`. The
multiplication is finely integrated operand scanning (FIOS) in radix `2³²`:
for each digit `aᵢ` of `a`, with `T` the accumulator (`n + 1` digits),

* `u = (t₀ + aᵢ b₀) (-m⁻¹) mod 2³²`, so that `T + aᵢ b + u m` is a multiple
  of `2³²`;
* one pass over the digits computes `T := (T + aᵢ b + u m) / 2³²`, with two
  carries: `x = tⱼ + aᵢ bⱼ + c₁` (`c₁ := x / 2³²`) and `y = (x mod 2³²) + u mⱼ
  + c₂` (`c₂ := y / 2³²`), whose low digit is stored one digit down;
* the top digit `tₙ` takes both carries.

After the `n` rounds, `T < 2 m` and `T 2^(64 w) ≡ a b (mod m)`; `T - m` is
computed into the temporary, digit by digit with the borrow in the sign bit
of a 64-bit difference, and the borrow out of the top digit selects `T` or
`T - m` with a mask.

Every loop counts a register down from a public count (`n`), every address
is a pointer plus a constant, and the pointers are the header's (loaded once,
at the start, before any store) advanced by 4 per digit, so only the
pointers and `w` affect timing.

The code takes a scratch buffer (`r8`, 72 bytes) where it saves the
nonvolatile `r14`–`r22`, keeping its address in `r21`.

Registers: `r5` `o`'s base, `r6` (advancing over) `a`, `r7` `b`'s base, `r8`
the accumulator's, `r9` the temporary's, `r10` `m`'s, `r11` `n`, `r12`
`-m⁻¹ mod 2³²`, `r4` the rounds left; in a round, `r14`–`r16` the pointers
into the accumulator, `b` and `m`, `r17` the digits left, `r18` `aᵢ`, `r19`
`u`, `r20` `c₁`, `r22` `c₂`, and `r0`, `r3` temporaries.
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

/-- The accumulator's first `w + 1` words (its digits `0` to `n + 1`) := 0. -/
def zeroAcc : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .lsr .d .r17 .r11 1, .addi .r17 .r17 1, .li .r0 0])
    (countLoop .r17 [.store .d .r0 .r14 0, .addi .r14 .r14 8])

/-! ## A round -/

/-- `aᵢ` into `r18`, then digit 0: `x = t₀ + aᵢ b₀`, `c₁ = x / 2³²`, `u = (x
mod 2³²) (-m⁻¹) mod 2³²`, and `c₂ = (x mod 2³² + u m₀) / 2³²` (the low digit
is 0); the pointers at digit 0 and `r17 := n - 1`. -/
def head : List Instr :=
  [.load .w .r18 .r6 0, .addi .r6 .r6 4,
    .load .w .r0 .r8 0, .load .w .r3 .r7 0, .mul .r3 .r18 .r3, .add .r0 .r0 .r3,
    .lsr .d .r20 .r0 32, .lsr .w .r0 .r0 0, .mul .r19 .r0 .r12, .lsr .w .r19 .r19 0,
    .load .w .r3 .r10 0, .mul .r3 .r19 .r3, .add .r0 .r0 .r3, .lsr .d .r22 .r0 32,
    .addi .r14 .r8 0, .addi .r15 .r7 0, .addi .r16 .r10 0, .subi .r17 .r11 1]

/-- Digit `j` (the pointers at digit `j - 1`): `x = tⱼ + aᵢ bⱼ + c₁`, `c₁ = x
/ 2³²`, `y = x mod 2³² + u mⱼ + c₂`, `c₂ = y / 2³²`, and `y mod 2³²` stored
as digit `j - 1`. -/
def step : List Instr :=
  [.load .w .r0 .r14 4, .load .w .r3 .r15 4, .mul .r3 .r18 .r3, .add .r0 .r0 .r3,
    .add .r0 .r0 .r20, .lsr .d .r20 .r0 32, .lsr .w .r0 .r0 0,
    .load .w .r3 .r16 4, .mul .r3 .r19 .r3, .add .r0 .r0 .r3, .add .r0 .r0 .r22,
    .lsr .d .r22 .r0 32, .store .w .r0 .r14 0,
    .addi .r14 .r14 4, .addi .r15 .r15 4, .addi .r16 .r16 4]

/-- The top digit `tₙ` (the accumulator's pointer at digit `n - 1`): `x = tₙ +
c₁`, `y = x mod 2³² + c₂`, `y mod 2³²` stored as digit `n - 1`, and `x / 2³² +
y / 2³²` as digit `n`. -/
def top : List Instr :=
  [.load .w .r0 .r14 4, .add .r0 .r0 .r20, .lsr .d .r20 .r0 32, .lsr .w .r0 .r0 0,
    .add .r0 .r0 .r22, .store .w .r0 .r14 0, .lsr .d .r0 .r0 32, .add .r0 .r0 .r20,
    .store .w .r0 .r14 4]

/-- One round: `T := (T + aᵢ b + u m) / 2³²`. -/
def round : Prog isa :=
  .seq (.block head) (.seq (countLoop .r17 step) (.block top))

/-- The `n` rounds, counted by `r4`. -/
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
