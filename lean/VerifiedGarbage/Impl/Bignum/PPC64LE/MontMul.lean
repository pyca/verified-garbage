module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Bignum.Layout

/-!
# Montgomery multiplication on PPC64LE

`vg_rsa_mont_mul(ws = r3, ws_len = r4, o = r5, a = r6, b = r7)` in the
working space of `Impl/Bignum/Layout.lean`: a header of 32 words, then eight
arrays of `w + 2` words, the modulus `m` in array 0, the accumulator in
array 2 and a temporary in array 3.

The multiplication is finely integrated operand scanning (FIOS) in radix
`2⁶⁴`, with the carries through `XER`'s CA (`addc`, `addze`). The
accumulator `T` is `w + 1` words: for each word `aᵢ` of `a`, one pass over
`T`, `b` and `m` computes `T := (T + aᵢ b + u m) / 2⁶⁴`:

* word 0: `s₀ = t₀ + aᵢ b₀ mod 2⁶⁴` and the first carry `c`, the high word
  of `t₀ + aᵢ b₀`; `u = s₀ (-m⁻¹) mod 2⁶⁴`, so that `s₀ + u m₀` is a multiple
  of `2⁶⁴`, and the second carry `d = (s₀ + u m₀) / 2⁶⁴`;
* words `j = 1` to `w - 1`: `x = tⱼ + aᵢ bⱼ + c` and `y = x mod 2⁶⁴ + u mⱼ +
  d`, each below `2¹²⁸` (`(2⁶⁴ - 1)² + 2 (2⁶⁴ - 1) = 2¹²⁸ - 1`), `c` and `d`
  their high words and the low word of `y` stored at word `j - 1`, so that
  each word of `T` is loaded and stored once; `(w - 1) mod 4` words one at a
  time, then the others four at a time;
* word `w`: `t_w + c + d`, stored at words `w - 1` and `w`.

`-m⁻¹ mod 2⁶⁴` is computed, in each round, from the header's `-m⁻¹ mod 2³²`
(`y`) by one step of Newton's iteration, `y (2 + m₀ y) mod 2⁶⁴`, since `m₀ y
(2 + m₀ y) + 1 = (m₀ y + 1)²`.

After the `w` rounds, `T < 2 m` and `T 2^(64 w) ≡ a b (mod m)`. Then `T -
m` is computed into the temporary word by word, with the borrow in CA
(`subfc`, `subfe`), and the borrow out of the top word `t_w` selects `T` or
`T - m` with a mask (`subfe` of a register from itself: all ones or 0).

Every loop counts a register down from a public count (`w + 1`, `w`, `(w -
1) mod 4`, `(w - 1) / 4`, from `n = 2 w`), every address is a pointer plus a
constant, and the pointers are the header's (loaded once, at the start,
before any store) advanced by 8 per word, so only the pointers and `w`
affect timing.

The code takes a scratch buffer (`r8`, 72 bytes) where it saves the
nonvolatile `r14`–`r22`, keeping its address in `r21`.

Registers: `r5` `o`'s base, `r6` (advancing over) `a`, `r7` `b`'s base, `r8`
the accumulator's, `r9` the temporary's, `r10` `m`'s, `r11` `n`, `r12`
`-m⁻¹ mod 2³²`; in the rounds, `r4` the rounds left, `r14`, `r15`, `r3` the
pointers into the accumulator, `b` and `m`, `r16` the words (or groups of
four) left, `r17` `aᵢ`, `r0` `u`, `r18` and `r22` the carries `c` and `d`,
`r19`, `r20` temporaries; in the final subtraction, `r14`–`r16` the pointers,
`r17` the words left, `r20` the mask, and `r0`, `r3` temporaries.
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

/-- The accumulator's first `w + 1` words := 0, and the rounds' count `w`
into `r4`. -/
def zeroAcc : Prog isa :=
  .seq (.block [.lsr .d .r4 .r11 1, .addi .r14 .r8 0, .addi .r17 .r4 1, .li .r22 0])
    (countLoop .r17 [.store .d .r22 .r14 0, .addi .r14 .r14 8])

/-! ## A round -/

/-- The start of a round, for `aᵢ` at `r6` (advanced): `aᵢ` into `r17`; `s₀ =
t₀ + aᵢ b₀ mod 2⁶⁴` into `r20` and the high word of `t₀ + aᵢ b₀` (the first
carry, `c`) into `r18`; `-m⁻¹ mod 2⁶⁴ = y (2 + m₀ y)` from `y = r12` into
`r22`, then `u = s₀ (-m⁻¹) mod 2⁶⁴` into `r0`; `(s₀ + u m₀) / 2⁶⁴` (the
second carry, `d`: the low word is 0) into `r22`; the pointers `r14`, `r15`,
`r3` at word 0 of `T`, `b` and `m`. -/
def fiosHead : List Instr :=
  [.load .d .r17 .r6 0, .addi .r6 .r6 8, .load .d .r19 .r7 0, .load .d .r20 .r8 0,
    .mul .r18 .r17 .r19, .mulhu .r19 .r17 .r19, .addc .r20 .r20 .r18, .addze .r18 .r19,
    .load .d .r3 .r10 0, .mul .r22 .r3 .r12, .addi .r22 .r22 2, .mul .r22 .r22 .r12, .mul .r0 .r20 .r22,
    .mul .r22 .r0 .r3, .mulhu .r19 .r0 .r3, .addc .r22 .r22 .r20, .addze .r22 .r19,
    .addi .r14 .r8 0, .addi .r15 .r7 0, .addi .r3 .r10 0]

/-- Word `j` of a round, the pointers at word `j - 1` less `k`: `x = tⱼ + aᵢ
bⱼ + c` (the words at `r14 + k + 8` and `r15 + k + 8`), `c` := its high word
and `y = x mod 2⁶⁴ + u mⱼ + d` (`mⱼ` at `r3 + k + 8`), `d` := its high word,
and its low word stored at `r14 + k`: word `j - 1` of `(T + aᵢ b + u m) /
2⁶⁴`. Each sum fits in 128 bits, `(2⁶⁴ - 1)² + 2 (2⁶⁴ - 1) = 2¹²⁸ - 1`, and
each high word of a product is at most `2⁶⁴ - 2`, so that adding a carry
to it does not carry. -/
def fiosStep (k : Nat) : List Instr :=
  [.load .d .r19 .r14 (k + 8), .addc .r18 .r18 .r19, .load .d .r19 .r15 (k + 8), .mul .r20 .r17 .r19,
    .mulhu .r19 .r17 .r19, .addze .r19 .r19, .addc .r20 .r20 .r18, .addze .r18 .r19,
    .load .d .r19 .r3 (k + 8), .addc .r22 .r22 .r20, .mul .r20 .r0 .r19, .mulhu .r19 .r0 .r19,
    .addze .r19 .r19, .addc .r20 .r20 .r22, .addze .r22 .r19, .store .d .r20 .r14 k]

/-- `U` words of a round, and the pointers advanced past them. -/
def fiosGroup (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => fiosStep (8 * k)) ++
    [.addi .r14 .r14 (8 * U), .addi .r15 .r15 (8 * U), .addi .r3 .r3 (8 * U)]

/-- The words of a round are done four at a time. -/
def unroll : Nat := 4

/-- `(w - 1) mod 4`, from `n = 2 w`, into `r16`. -/
def fiosRem : List Instr := [.lsr .d .r16 .r11 1, .subi .r16 .r16 1, .lsl .r16 .r16 62, .lsr .d .r16 .r16 62]

/-- `(w - 1) / 4` into `r16`. -/
def fiosQuot : List Instr := [.lsr .d .r16 .r11 1, .subi .r16 .r16 1, .lsr .d .r16 .r16 2]

/-- Word `w` (above `r14`, at word `w - 1`) plus both carries, stored at
words `w - 1` and `w`. -/
def fiosTop : List Instr :=
  [.load .d .r19 .r14 8, .addc .r18 .r18 .r19, .li .r19 0, .addze .r19 .r19, .addc .r18 .r18 .r22,
    .addze .r19 .r19, .store .d .r18 .r14 0, .store .d .r19 .r14 8]

/-- `if r16 ≠ 0` then `r16` times `body`. -/
def countLoop? (body : List Instr) : Prog isa :=
  .ite (.zero .d .r16) (.block []) (countLoop .r16 body)

/-- One round: `T := (T + aᵢ b + u m) / 2⁶⁴`, finely integrated (FIOS): words
`1` to `w - 1` one at a time (`(w - 1) mod 4` of them), then four at a
time. -/
def round : Prog isa :=
  .seq (.block (fiosHead ++ fiosRem))
    (.seq (countLoop? (fiosGroup 1)) (.seq (.block fiosQuot) (.seq (countLoop? (fiosGroup unroll))
      (.block fiosTop))))

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

/-- `[tmp] = T - m` over `w` words, the borrow in `XER`'s CA (`subc` of a
register from itself sets it: no borrow), then `r20` := all ones if `T < m`
(the top word `t_w` minus the borrow borrows: CA clear), else 0 (`sube` of
a register from itself is `CA - 1`). -/
def subMod64 : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r10 0, .lsr .d .r17 .r11 1, .subc .r0 .r0 .r0])
    (.seq (countLoop .r17 [.load .d .r0 .r14 0, .load .d .r3 .r16 0, .sube .r0 .r0 .r3, .store .d .r0 .r15 0,
        .addi .r14 .r14 8, .addi .r15 .r15 8, .addi .r16 .r16 8])
      (.block [.load .d .r0 .r14 0, .li .r3 0, .sube .r0 .r0 .r3, .sube .r20 .r20 .r20]))

/-- `[o] = mask ? T : [tmp]`, word by word, the mask in `r20`. -/
def selectAcc64 : Prog isa :=
  .seq (.block [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r5 0, .lsr .d .r17 .r11 1])
    (countLoop .r17 [.load .d .r0 .r15 0, .load .d .r3 .r14 0, .logic .xor .r3 .r3 .r0,
      .logic .and .r3 .r3 .r20, .logic .xor .r3 .r3 .r0, .store .d .r3 .r16 0,
      .addi .r14 .r14 8, .addi .r15 .r15 8, .addi .r16 .r16 8])

/-- The arithmetic, after the bases are loaded. -/
def tail : Prog isa := .seq zeroAcc (.seq rounds (.seq subMod64 selectAcc64))

/-- `vg_rsa_mont_mul(ws, ws_len, o, a, b, scratch)`: `[o] = [a] [b] R⁻¹ mod m`
for `R = 2^(64 w)`. -/
def mul : Prog isa :=
  .seq (.block save) (.seq (.seq (.block args) (.seq (.block loads) tail)) (.block restore))

end VG.Impl.Bignum.PPC64LE
