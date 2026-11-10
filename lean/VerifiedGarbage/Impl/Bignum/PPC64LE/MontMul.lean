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
`2⁶⁴`. The accumulator `T` is `w + 1` words: for each word `aᵢ` of `a`, one
pass over `T`, `b` and `m` computes `T := (T + aᵢ b + u m) / 2⁶⁴`:

* word 0 (`head`): `s₀ = t₀ + lo(aᵢ b₀)`; `u = s₀ (-m⁻¹) mod 2⁶⁴`, so that
  `s₀ + lo(u m₀)` is a multiple of `2⁶⁴`;
* words `1` to `w - 1` in blocks of `k ≤ 4` words (`block`): one block of
  `(w - 1) mod 4` words, then blocks of four. A block adds `aᵢ b + u m` to
  its words with four carry chains, each one `adde` per word: the low words
  of `aᵢ bⱼ`, their high words (one word up), the low words of `u mⱼ` and
  their high words. What a chain leaves for the next block is pending: the
  carries of the two low chains (in `r12` and `r11`, as `CA - 1`), and the
  last high words, with the carries of the high chains added (`r20` and
  `r22`). Each word is loaded and stored once, one word down;
* word `w` (`top`): `t_w` plus the pending values, stored at words `w - 1`
  and `w`.

`m' = -m⁻¹ mod 2⁶⁴` is computed once (`mPrime`), from the header's `-m⁻¹ mod
2³²` (`y`, in `r12`) by one step of Newton's iteration, `y (2 + m₀ y) mod
2⁶⁴`, since `m₀ y (2 + m₀ y) + 1 = (m₀ y + 1)²`, into the accumulator's word
`w + 1`, which `T` does not use, and each round loads it from there. After
the rounds, `r22 := m'` and `r12 := m' mod 2³²`, which is `y` again
(`restoreMinv`).

After the `w` rounds, `T < 2 m` and `T 2^(64 w) ≡ a b (mod m)`. Then `T -
m` is computed into the temporary word by word, with the borrow in CA
(`subfc`, `subfe`), and the borrow out of the top word `t_w` selects `T` or
`T - m` with a mask (`subfe` of a register from itself: all ones or 0).

Every loop counts down from a public count (`w + 1`, `w`, `(w - 1) mod 4`,
`(w - 1) / 4`, from `n = 2 w`), every address is a pointer plus a constant,
and the pointers are the arguments' advanced by 8 per word, so only the
pointers and `w` affect timing.

Registers: `r5` `o`'s base, `r6` (advancing over) `a`, `r7` `b`'s base, `r8`
the accumulator's, `r9` the temporary's, `r10` `m`'s, `r11` `n`, `r12` `-m⁻¹
mod 2³²`, but in the rounds (see "A round"); in the final subtraction,
`r14`–`r16` the pointers, `r17` the words left, `r20` the mask, and `r0`,
`r3` temporaries.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE

open VG.PPC64LE VG.Impl.Bignum

/-! ## Saving and restoring the nonvolatile registers -/

/-- The nonvolatile registers used, in the order they are saved: `r21` keeps
the scratch buffer's address. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r21].getD i .r14

/-! ## The arguments -/

/-! ## Loops -/

/-- `do body; cnt -= 1 while cnt ≠ 0`, for `cnt` at least 1. -/
def countLoop (cnt : Reg) (body : List Instr) : Prog isa :=
  .loop (.block (body ++ ([.subi cnt cnt 1] : List Instr))) (.nonzero .d cnt)

/-- `m' = -m⁻¹ mod 2⁶⁴ = y (2 + m₀ y)` from `y = r12` into `r22`, and stored
in the accumulator's word `w + 1` (`r14 := r8 + 8 w`), above the `w + 1`
words of `T`, which the rounds do not write. -/
def mPrime : List Instr :=
  [.load .d .r3 .r10 0, .mul .r22 .r3 .r12, .addi .r22 .r22 2, .mul .r22 .r22 .r12, .lsl .r14 .r11 2,
    .add .r14 .r14 .r8, .store .d .r22 .r14 8]

/-- `r12 := m' mod 2³²`, which is `y` again (`m₀ y ≡ -1`, so `y (2 + m₀ y) ≡
y (mod 2³²)`). -/
def restoreMinv : List Instr := [.lsl .r12 .r22 32, .lsr .d .r12 .r12 32]

/-- The zeroing of the accumulator's first `w + 1` words, from `r3 = 0`. -/
def zeroAccPre : List Instr := [.lsr .d .r4 .r11 1, .addi .r14 .r8 0, .addi .r17 .r4 1, .li .r3 0]

/-- `mPrime`, then the accumulator's first `w + 1` words := 0, and the
rounds' count `w` into `r4`. -/
def zeroAcc : Prog isa :=
  .seq (.block (mPrime ++ zeroAccPre)) (countLoop .r17 [.store .d .r3 .r14 0, .addi .r14 .r14 8])

/-! ## A round

The rounds keep in registers only the values that the taint analysis of
their callers must see as public, or that the code computes from public
ones: the pointers, the counts, `m`'s base `r10` and `o`'s `r5`. Everything
else they need is derived from those (`8 w` is the distance `r16 - r10`
moves over a round, the accumulator's base `r10 + 16 (w + 2)`) or is
secret, as `m'`, kept in the accumulator's word `w + 1` (`mPrime`). The
callers' registers `r21` and `r23`–`r31` are never written by `rounds`, and
the kernel's rounds (`roundsK`) write only `r2` and `r23`–`r31`, which the
kernel restores from vector registers: so a caller's public register stays
public.

Registers in the rounds: `r6` `a` (advancing), `r14` the accumulator, at
word `j - 1` of `T` while word `j` is next, `r15` and `r16` `b` and `m`, at
word `j`, `r17` the rounds left in its high half and, in its low half, the
blocks of four (or, in `rounds8`, eight) words left; `r18` `aᵢ` and `r19`
`u`; `r20`, `r12`, `r22`, `r11` the pending values (below): `r3`, `r4`,
`r7`, `r8` (and `r28`–`r31` in a block of eight) the words of a block
(`sreg`), `r9` and `r0` temporaries. -/

/-- The registers of the words of a block: `r28`–`r31` only in blocks of
eight, which only the kernel's rounds (`rounds8`) run, between its saves and
restores of them (`kernelSave`, `kernelRestore`). -/
def sreg (i : Nat) : Reg := [.r3, .r4, .r7, .r8, .r28, .r29, .r30, .r31].getD i .r8

/-- Word `i` of a block's low products: `S i += lo(x pᵢ) + CA`, `pᵢ` loaded
into `r9`. -/
def loStep (x p : Reg) (i : Nat) : List Instr :=
  [.load .d .r9 p (8 * i), .mul .r0 x .r9, .adde (sreg i) (sreg i) .r0]

/-- Word `i + 1` of a block's high products: `S (i + 1) += hi(x pᵢ) + CA`. -/
def hiStep (x p : Reg) (i : Nat) : List Instr :=
  [.load .d .r0 p (8 * i), .mulhu .r0 x .r0, .adde (sreg (i + 1)) (sreg (i + 1)) .r0]

/-- Half of a block of `k` words: `S += x p + c + h` for the `k` words `p`
at the register `p`. Two carry chains, each one pass of `adde` over the
block's words: the low words of the products, with the carry `c` in and
out, kept in `c` as `CA - 1` (`subfe c, c, c`: 0 or all ones, restored by
`subfc c, c, r10`, which carries iff `c` is 0, `r10` not being all ones),
and the high words, one word up, from the pending high word `h` and into
it, `h := hi(x pₖ₋₁) + CA`, which does not overflow (a high word is at
most `2⁶⁴ - 2`). -/
def half (c x p h : Reg) (k : Nat) : List Instr :=
  [.subc c .r10 c] ++ (List.range k).flatMap (loStep x p) ++ ([.mulhu .r9 x .r9, .sube c c c, .addc .r3 .r3 h] : List Instr) ++
    (List.range (k - 1)).flatMap (hiStep x p) ++ ([.addze h .r9] : List Instr)

/-- A block of `k ≤ 8` words: words `j` to `j + k - 1` of `T`, loaded,
`T + aᵢ b + u m` added (`half` with `aᵢ` and `b`, then `u` and `m`), stored
one word down, and the pointers advanced. -/
def block (k : Nat) : List Instr :=
  (List.range k).map (fun i => .load .d (sreg i) .r14 (8 * i + 8)) ++ half .r12 .r18 .r15 .r20 k ++
    half .r11 .r19 .r16 .r22 k ++ (List.range k).map (fun i => .store .d (sreg i) .r14 (8 * i)) ++
    ([.addi .r14 .r14 (8 * k), .addi .r15 .r15 (8 * k), .addi .r16 .r16 (8 * k)] : List Instr)

/-- The start of a round, `r16` and `r15` at word `w` of `m` and `b`: `8 w`
into `r9`, the pointers at word 0 (`r14` at the accumulator's base, `r10 + 2
(8 w) + 32`), `m'` from the accumulator's word `w + 1` into `r19`, `(w - 1) /
4` added to `r17` and `(w - 1) mod 4` into `r9`. -/
def roundStart : List Instr :=
  [.sub .r9 .r16 .r10, .addi .r16 .r10 0, .sub .r15 .r15 .r9, .add .r3 .r9 .r9, .add .r3 .r3 .r10,
    .addi .r14 .r3 32, .add .r4 .r3 .r9, .load .d .r19 .r4 40, .lsr .d .r7 .r9 3, .subi .r7 .r7 1,
    .lsr .d .r8 .r7 2, .add .r17 .r17 .r8, .lsl .r9 .r7 62, .lsr .d .r9 .r9 62]

/-- Word 0: `aᵢ` into `r18` (`r6` advanced); `s₀ = t₀ + lo(aᵢ b₀)` into `r3`,
its carry kept in `r12` and `hi(aᵢ b₀)` in `r20`; `u = s₀ m'` into `r19`;
`s₀ + lo(u m₀)`, a multiple of `2⁶⁴`, its carry kept in `r11` and
`hi(u m₀)` in `r22`; `b`'s and `m`'s pointers at word 1. -/
def head : List Instr :=
  [.load .d .r18 .r6 0, .addi .r6 .r6 8, .load .d .r3 .r14 0, .load .d .r0 .r15 0, .mulhu .r20 .r18 .r0,
    .mul .r0 .r18 .r0, .addc .r3 .r3 .r0, .sube .r12 .r12 .r12, .mul .r19 .r19 .r3, .load .d .r0 .r16 0,
    .mulhu .r22 .r19 .r0, .mul .r0 .r19 .r0, .addc .r3 .r3 .r0, .sube .r11 .r11 .r11, .addi .r15 .r15 8,
    .addi .r16 .r16 8]

/-- Words `1` to `(w - 1) mod 4` (`r9`), one block of that many. -/
def remBlock : Prog isa :=
  .ite (.zero .d .r9) (.block []) (.seq (.block [.subi .r9 .r9 1]) (.ite (.zero .d .r9) (.block (block 1))
    (.seq (.block [.subi .r9 .r9 1]) (.ite (.zero .d .r9) (.block (block 2)) (.block (block 3))))))

/-- The other words, four at a time, counted by `r17`'s low half. -/
def quadLoop : Prog isa :=
  .ite (.zero .w .r17) (.block []) (.loop (.block (block 4 ++ ([.subi .r17 .r17 1] : List Instr))) (.nonzero .w .r17))

/-- Word `w` (above `r14`, at word `w - 1`) plus the pending values, stored
at words `w - 1` and `w`; then one round less in `r17`'s high half, and
`r9` := the rounds left. -/
def top : List Instr :=
  [.load .d .r3 .r14 8, .li .r4 0, .subc .r12 .r10 .r12, .adde .r3 .r3 .r20, .addze .r4 .r4,
    .subc .r11 .r10 .r11, .adde .r3 .r3 .r22, .addze .r4 .r4, .store .d .r3 .r14 0, .store .d .r4 .r14 8,
    .li .r9 1, .lsl .r9 .r9 32, .sub .r17 .r17 .r9, .lsr .d .r9 .r17 32]

/-- One round: `T := (T + aᵢ b + u m) / 2⁶⁴`, by blocks of words with four
carry chains. -/
def round : Prog isa :=
  .seq (.block (roundStart ++ head)) (.seq remBlock (.seq quadLoop (.block top)))

/-- Before the rounds: `r16` and `r15` at word `w` of `m` and `b`, as a round
leaves them, and `w` rounds in `r17`'s high half, from `r4 = w`. -/
def roundsInit : List Instr :=
  [.lsl .r9 .r11 2, .add .r16 .r10 .r9, .add .r15 .r7 .r9, .lsl .r17 .r4 32]

/-- After the rounds: `2 w` back in `r11`, the bases of `b`, the accumulator
and the temporary back in `r7`, `r8` and `r9`, all from `8 w = r16 - r10`,
and `m'` in `r22`. -/
def roundsFini : List Instr :=
  [.sub .r3 .r16 .r10, .lsr .d .r11 .r3 2, .sub .r7 .r15 .r3, .add .r8 .r3 .r3, .add .r8 .r8 .r10,
    .addi .r8 .r8 32, .add .r9 .r8 .r3, .addi .r9 .r9 16, .add .r4 .r8 .r3, .load .d .r22 .r4 8]

/-- The `w` rounds. -/
def rounds : Prog isa :=
  .seq (.block roundsInit) (.seq (.loop round (.nonzero .d .r9)) (.block roundsFini))

/-! ### The kernel's rounds: blocks of eight words

For `w` not a multiple of 4 (`roundsK`), the kernel (`kernel`), which saves
`r27` and `r28`–`r31` in vector registers, runs the rounds with them: words `1` to `w - 1` in one block of `(w - 1) mod 4`
(`remBlock`, counted by `r9`, which every block uses as a temporary), one
block of four if `w - 1` has bit 2 (`quadBlock`, the bit in `r27`, which no
block writes), then blocks of eight (`octLoop`, in `sreg 0` to `sreg 7`). -/

/-- `roundStart`, with `(w - 1) / 8` added to `r17` and bit 2 of `w - 1` into
`r27`. -/
def roundStart8 : List Instr :=
  [.sub .r9 .r16 .r10, .addi .r16 .r10 0, .sub .r15 .r15 .r9, .add .r3 .r9 .r9, .add .r3 .r3 .r10,
    .addi .r14 .r3 32, .add .r4 .r3 .r9, .load .d .r19 .r4 40, .lsr .d .r7 .r9 3, .subi .r7 .r7 1,
    .lsr .d .r8 .r7 3, .add .r17 .r17 .r8, .lsl .r27 .r7 61, .lsr .d .r27 .r27 63, .lsl .r9 .r7 62,
    .lsr .d .r9 .r9 62]

/-- One block of four words if `r27` is not 0. -/
def quadBlock : Prog isa := .ite (.zero .d .r27) (.block []) (.block (block 4))

/-- The other words, eight at a time, counted by `r17`'s low half. -/
def octLoop : Prog isa :=
  .ite (.zero .w .r17) (.block []) (.loop (.block (block 8 ++ ([.subi .r17 .r17 1] : List Instr))) (.nonzero .w .r17))

/-- `round`, by blocks of up to eight words. -/
def round8 : Prog isa :=
  .seq (.block (roundStart8 ++ head)) (.seq remBlock (.seq quadBlock (.seq octLoop (.block top))))

/-- The `w` rounds, by blocks of up to eight words. -/
def rounds8 : Prog isa :=
  .seq (.block roundsInit) (.seq (.loop round8 (.nonzero .d .r9)) (.block roundsFini))

/-! ### The kernel's rounds: four rows at a time

For `w` a multiple of 4, the kernel (`kernel`) runs the rounds four words
of `a` at a time, as `w / 4` groups: a group replaces `T` with `(T + A b + U
m) / 2²⁵⁶`, for `A` the group's four words of `a` and `U` four words chosen
so that `T + A b + U m` is a multiple of `2²⁵⁶`. A group goes over `T`, `b`
and `m` in chunks of four words, and over its four words of `a` (its rows) in
each chunk, so that each word of `T`, `b` and `m` is loaded once a group,
not once a word of `a`: the chunk's four words of `b` and `m` in registers,
the window of `T` it adds to in five accumulators, `r27`–`r31` (`accR`).

A row adds `aᵢ b + uᵢ m`, for the chunk's words of `b` and `m`, to the
window, and moves it down a word (`mulB`, `loM`, `shiftM`). In the first
chunk (`chunk0`), the row computes `uᵢ` from the window's low word and `m'`,
which zeroes that word, and stores `uᵢ` in the word of `T` the chunk has
loaded, for the next chunks; in the others (`chunkT`), the low word is a
word of the new `T`, stored a chunk down, and the row moves `uᵢ` a chunk up,
to the word the chunk has loaded. The group's top (`groupEnd`) adds `T`'s
top word, `t_w`, to the window, and stores it as the new `T`'s four top
words, and its carry as `t_w`. The kernel's callers' registers that the
rounds write, `r2` and `r23`–`r31`, are kept in vector registers
(`kernelSave`, `kernelRestore`).

Registers: `r0` zero, `r6` `a` (advancing a group at a time), `r7` and `r12`
the chunk's words of `b` and `m`, `r9` `T`, a chunk down, `r3` the chunks
left and `r4` the groups left; `r14`–`r17` the words of `b` (`bR`) and `r18`,
`r19`, `r20`, `r2` those of `m` (`mR`), `r23` `m'`, `r24` `aᵢ`, `r25` `uᵢ`,
`r26` the carry out of the window (with CA, the window's weight-`2²⁵⁶` part),
`r22` a temporary. -/

/-- The window, from its low word. -/
def accR (j : Nat) : Reg := [.r27, .r28, .r29, .r30, .r31].getD j .r31

/-- The chunk's words of `b`. -/
def bR (j : Nat) : Reg := [.r14, .r15, .r16, .r17].getD j .r17

/-- The chunk's words of `m`. -/
def mR (j : Nat) : Reg := [.r18, .r19, .r20, .r2].getD j .r2

/-- `dst := src + (lo or hi) (p x)` over four words, as a carry chain (the
first word with `addc`), the products in `r22`. -/
def prodChain (hi : Bool) (x : Reg) (p dst src : Nat → Reg) : List Instr :=
  (List.range 4).flatMap fun j =>
    [(if hi then Instr.mulhu else Instr.mul) .r22 (p j) x, (if j = 0 then Instr.addc else Instr.adde) (dst j) (src j) .r22]

/-- The window's low four words += `aᵢ b` (`aᵢ` in `r24`), into five words. -/
def mulB : List Instr :=
  prodChain false .r24 bR accR accR ++ ([.addze (accR 4) .r0] : List Instr) ++
    prodChain true .r24 bR (fun j => accR (j + 1)) (fun j => accR (j + 1))

/-- The window += the low words of `uᵢ m` (`uᵢ` in `r25`), with `r26` added at
word 4 and its carry into `r26`. -/
def loM : List Instr :=
  prodChain false .r25 mR accR accR ++ ([.adde (accR 4) (accR 4) .r26, .addze .r26 .r0] : List Instr)

/-- The window moved down a word, the high words of `uᵢ m` added: the carry
out in CA. -/
def shiftM : List Instr := prodChain true .r25 mR accR (fun j => accR (j + 1))

/-- Row `r` of the first chunk: `uᵢ` from the window's low word and `m'`,
stored at word `r` of `T` (`r9`). -/
def row0 (r : Nat) : List Instr :=
  ([.addze .r26 .r26, .load .d .r24 .r6 (8 * r)] : List Instr) ++ mulB ++
    ([.mul .r25 .r27 .r23, .store .d .r25 .r9 (8 * r)] : List Instr) ++ loM ++ shiftM

/-- Row `r` of a later chunk: `uᵢ` moved from word `r` of the chunk below
(`r9`) to word `r` of this chunk, and the window's low word stored there. -/
def rowT (r : Nat) : List Instr :=
  ([.addze .r26 .r26, .load .d .r24 .r6 (8 * r), .load .d .r25 .r9 (8 * r), .store .d .r25 .r9 (8 * r + 32)] :
    List Instr) ++ mulB ++ loM ++ ([.store .d .r27 .r9 (8 * r)] : List Instr) ++ shiftM

/-- The chunk's words of `b` and `m` loaded, and their pointers advanced. -/
def loadBM : List Instr :=
  (List.range 4).map (fun j => .load .d (bR j) .r7 (8 * j)) ++ (List.range 4).map (fun j => .load .d (mR j) .r12 (8 * j)) ++
    ([.addi .r7 .r7 32, .addi .r12 .r12 32] : List Instr)

/-- The first chunk of a group: `r9` and `r12` at the bases of `T` and `m`,
`m'` from the accumulator's word `w + 1`, the chunks left, `w / 4 - 1`, into
`r3`, the window `T`'s low four words, and its four rows. -/
def chunk0 : List Instr :=
  ([.addi .r9 .r8 0, .addi .r12 .r10 0, .lsl .r22 .r11 2, .add .r22 .r22 .r8, .load .d .r23 .r22 8,
      .lsr .d .r3 .r11 3, .subi .r3 .r3 1] : List Instr) ++
    loadBM ++ (List.range 4).map (fun j => .load .d (accR j) .r9 (8 * j)) ++
    ([.li .r26 0, .addc .r27 .r27 .r0] : List Instr) ++ (List.range 4).flatMap row0

/-- The chunk's four words of `T` added to the window. -/
def addT : List Instr :=
  .addze .r26 .r26 :: (List.range 4).flatMap fun j =>
    [.load .d .r22 .r9 (8 * j + 32), (if j = 0 then Instr.addc else Instr.adde) (accR j) (accR j) .r22]

/-- A later chunk: its words of `T` added to the window, its four rows, and
`r9` a chunk up. -/
def chunkT : List Instr :=
  addT ++ loadBM ++ (List.range 4).flatMap rowT ++ ([.addi .r9 .r9 32] : List Instr)

/-- The chunks after the first, counted by `r3`. -/
def chunkLoop : Prog isa :=
  .ite (.zero .d .r3) (.block []) (countLoop .r3 chunkT)

/-- The group's top: `t_w` added to the window, its four words stored at
words `w - 4` to `w - 1` of `T` and its carry at word `w`; `b`'s pointer
back to its base, `a`'s a group on, and one group less in `r4`. -/
def groupEnd : List Instr :=
  [.addze .r26 .r26, .load .d .r22 .r9 32, .addc .r27 .r27 .r22, .addze .r28 .r28, .addze .r29 .r29,
    .addze .r30 .r30, .addze .r26 .r26, .store .d .r27 .r9 0, .store .d .r28 .r9 8, .store .d .r29 .r9 16,
    .store .d .r30 .r9 24, .store .d .r26 .r9 32, .lsl .r22 .r11 2, .sub .r7 .r7 .r22, .addi .r6 .r6 32,
    .subi .r4 .r4 1]

/-- One group. -/
def group : Prog isa := .seq (.block chunk0) (.seq chunkLoop (.block groupEnd))

/-- The `w / 4` groups, from `r0 := 0` and the count in `r4`; then the
temporary's base back in `r9`, and `m'` in `r22`. -/
def rounds4 : Prog isa :=
  .seq (.block [.li .r0 0, .lsr .d .r4 .r11 3]) (.seq (.loop group (.nonzero .d .r4))
    (.block [.lsl .r22 .r11 2, .add .r9 .r8 .r22, .load .d .r22 .r9 8, .addi .r9 .r9 16]))

/-- The kernel's rounds: `rounds4` if `w` is a multiple of 4 (`w mod 4`, from
`n = 2 w`, in `r3`), else `rounds8`. -/
def roundsK : Prog isa :=
  .seq (.block [.lsl .r3 .r11 61, .lsr .d .r3 .r3 62]) (.ite (.zero .d .r3) rounds4 rounds8)

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

/-- `restoreMinv`, then `subMod64`, in the same pieces as `subMod64`. -/
def subMod64M : Prog isa :=
  .seq (.block (restoreMinv ++ [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r10 0, .lsr .d .r17 .r11 1, .subc .r0 .r0 .r0]))
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
def tail : Prog isa := .seq zeroAcc (.seq rounds (.seq subMod64M selectAcc64))

/-- `tail` with the kernel's rounds (`roundsK`), which write `r2` and
`r23`–`r31`: the kernel's. -/
def tail8 : Prog isa := .seq zeroAcc (.seq roundsK (.seq subMod64M selectAcc64))

/-! ## The shared kernel

`montOp` (`PublicChecked.lean`) calls `tail` as one function, `kernel`,
rather than inlining it: a call may change `r0`, `r11` and `r12` on the way
(linkage code, see `TCB/PPC64LE/Isa.lean`), so the caller passes `2 w` in
`r4` and `-m⁻¹ mod 2³²` in `r3`, and its own return address in `r14`, which
the kernel keeps in the temporary's word `w + 1` (`r9 + 8 w + 8`), which
`tail` does not write, and loads again at its end. `tail` leaves `r12` as
it found it (`restoreMinv`), and `r11` is `2 w` again. -/

/-- `r12 := r3`, `r11 := r4`, and `r14` stored in the temporary's word
`w + 1`. -/
def kernelEntry : List Instr :=
  [.addi .r12 .r3 0, .addi .r11 .r4 0, .lsl .r3 .r4 2, .add .r3 .r9 .r3, .store .d .r14 .r3 8]

/-- `r14` loaded again from the temporary's word `w + 1`. -/
def kernelExit : List Instr := [.lsl .r3 .r11 2, .add .r3 .r9 .r3, .load .d .r14 .r3 8]

/-- The callers' registers that `tail8` writes, and the vector registers
the kernel keeps them in. -/
def kernelSaved : List (VReg × Reg) :=
  [(.v0, .r27), (.v1, .r28), (.v2, .r29), (.v3, .r30), (.v4, .r31), (.v5, .r2), (.v6, .r23), (.v7, .r24),
    (.v8, .r25), (.v9, .r26)]

/-- `kernelSaved`'s registers into their vector registers (`mtvsrd`). -/
def kernelSave : List Instr := kernelSaved.map fun (v, r) => .mtvsrd v r

/-- `kernelSaved`'s registers back from their vector registers (`mfvsrd`). -/
def kernelRestore : List Instr := kernelSaved.map fun (v, r) => .mfvsrd r v

/-- `tail8` between `kernelEntry` and `kernelExit`. -/
def kernelBody : Prog isa := .seq (.block kernelEntry) (.seq tail8 (.block kernelExit))

/-- The kernel: `kernelBody` between `kernelSave` and `kernelRestore`. -/
def kernel : Prog isa := .seq (.block kernelSave) (.seq kernelBody (.block kernelRestore))

/-- The name of the kernel's function. -/
def kernelName : String := "vg_rsa_mont_kernel"

end VG.Impl.Bignum.PPC64LE
