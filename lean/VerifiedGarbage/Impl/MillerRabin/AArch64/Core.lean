module

public import VerifiedGarbage.Impl.MillerRabin.AArch64.Layout
public import VerifiedGarbage.Impl.Rsa.AArch64.Crt
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys

/-! # Shared fixed-window Miller–Rabin computation

Witness sampling and round counts belong to the callers. The namespace is
retained for compatibility with the existing RSA proofs. -/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.Candidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Keys

/-! ## Miller–Rabin's exponent

For `c − 1 = m 2^a` (`m` odd), the exponentiation is by `E = (c − 1) / 2^σ`
for `σ ∈ [1, 4]`, `σ ≡ a (mod 4)`: `E = m 2^(a − σ)` has its lowest set bit
at a multiple of 4, where a window of 4 bits ends. `σ` is secret: `E` is
`c / 2` halved under the masks of `σ > 1`, `σ > 2` and `σ > 3`, which
come from the lowest set bit `l = 2^(a mod 64)` of the lowest nonzero word
of `c − 1` (`l & K ≠ 0` for the constants `K` of `sigK`). -/

/-- `x5 := ` the lowest nonzero word of `c − 1` (`c`'s words, bit 0 of the
first flipped): `x5 |= word & mask (x5 = 0)` from the bottom (`x7 = 0`,
`x8` all ones, `x4 = 1`). -/
def lowWord : List (Prog isa) := [
  .block (ws ++ base aN .x16 ++ [ld .x5 .x16, movi .x4 1, .logic .eor .x .x5 .x5 .x4, next .x16,
    .subImm .x .x14 .x12 1, movi .x7 0, .subImm .x .x8 .x7 1]),
  countLoop .x14 [ld .x3 .x16, .subs .x .x6 .x5 .x4, .csel .x .x6 .x7 .x8, .logic .and .x .x3 .x3 .x6,
    .logic .orr .x .x5 .x5 .x3, next .x16]]

/-- The masks of `σ > j` (`j = 1, 2, 3`) are those of `l & sigK j ≠ 0`: the
bits whose position mod 4 is 0, 2 or 3; 0 or 3; 0. -/
def sigK (j : Nat) : Nat :=
  if j = 1 then 0xDDDDDDDDDDDDDDDD else if j = 2 then 0x9999999999999999 else 0x1111111111111111

/-- `x4 := sigK j`, 16 bits at a time. -/
def ldK (j : Nat) : List Instr :=
  [.movz .x .x4 (BitVec.ofNat 16 (sigK j)) 0, .movk .x .x4 (BitVec.ofNat 16 (sigK j / 2 ^ 16)) 1,
    .movk .x .x4 (BitVec.ofNat 16 (sigK j / 2 ^ 32)) 2, .movk .x .x4 (BitVec.ofNat 16 (sigK j / 2 ^ 48)) 3]

/-- `[x17] := x15 ? [x16] / 2 : [x16]` over `w` words (`x12`), in place when
`x17 = x16`: the word below is written once the next is read, the word in
`x5`. -/
def halfPass : List (Prog isa) := [
  .block [ld .x5 .x16, next .x16, .subImm .x .x14 .x12 1],
  countLoop .x14 [ld .x3 .x16, .lsl .x .x4 .x3 63, .lsr .x .x6 .x5 1, .logic .orr .x .x6 .x6 .x4,
    .logic .eor .x .x6 .x6 .x5, .logic .and .x .x6 .x6 .x15, .logic .eor .x .x6 .x6 .x5, st .x6 .x17, next .x16,
    next .x17, mov .x5 .x3],
  .block [.lsr .x .x6 .x5 1, .logic .eor .x .x6 .x6 .x5, .logic .and .x .x6 .x6 .x15, .logic .eor .x .x6 .x6 .x5,
    st .x6 .x17]]

/-- `[aE] := [aE] / 2` under the mask of `σ > j`, `aE`'s base in `x10`, `l`'s
address in `x9` (`x7 = 0`, `x8` all ones). -/
def halfCond (j : Nat) : List (Prog isa) :=
  .block (ldK j ++ [ld .x3 .x9, .logic .and .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4,
    .csel .x .x15 .x8 .x7, mov .x16 .x10, mov .x17 .x10]) :: halfPass

/-- `l` after the `w` words of `aE`, then `[aE] := E`: `c / 2` (from `aN`),
then the halvings, `aE`'s base kept in `x10`. -/
def expSetup : List (Prog isa) :=
  lowWord ++ [
  .block (base aE .x10 ++ [.sub .x .x6 .x7 .x5, .logic .and .x .x6 .x6 .x5, .lsl .x .x9 .x12 3,
    .add .x .x9 .x10 .x9, st .x6 .x9, mov .x15 .x8, mov .x17 .x10] ++ base aN .x16)] ++
  halfPass ++ halfCond 1 ++ halfCond 2 ++ halfCond 3

/-! ## Miller–Rabin -/

/-- `x15 :=` the mask of `[aY] = [j]`. -/
def eqMask (j : Nat) : List (Prog isa) :=
  eqA aY j ++ ([.block ([movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask)] : List (Prog isa))

/-- `y := y²`, the flag or'ed with `y = −1`. -/
def mrSq (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul aY aY aY] ++ eqMask aRm1 ++ [.block [ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x15, sth .x4 kFlag]]

/-- `[aXm] := T_d` for the digit `d` in `kG`: for each entry `j` (`x10`, its
base in `x2`), `[aXm] := T_j` under the mask of `j = d` (all ones iff
`j ⊕ d − 1` borrows). -/
def mrSel : List (Prog isa) := [
  .block (ws ++ base aT0 .x2 ++ base aXm .x13 ++ [ldh .x9 kG, movi .x10 0, movi .x7 0, .subImm .x .x8 .x7 1]),
  .loop (seqs [
    .block [.logic .eor .x .x3 .x10 .x9, movi .x4 1, .subs .x .x3 .x3 .x4, .csel .x .x15 .x7 .x8, mov .x16 .x2,
      mov .x17 .x13, mov .x14 .x12],
    Crt.selLoop,
    .block [.add .x .x2 .x2 .x11, .addImm .x .x10 .x10 1, .subImm .x .x3 .x10 16]]) (.nonzero .x .x3)]

/-- One window, the digit `d` at the top of `kV`: four squarings, `T_d` into
`aXm` by masks, `y := y T_d`; the flag `P := d ≠ 0 ? (y = 1 ∨ y = −1) : P`;
then `kV := kV << 4` and `x3 := kBits := kBits − 1`. -/
def mrWin (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  mrSq mul ++ mrSq mul ++ mrSq mul ++ mrSq mul ++
  [.block [ldh .x3 kV, .lsr .x .x3 .x3 60, sth .x3 kG]] ++ mrSel ++
  [mul aY aY aXm] ++ eqMask aRm1 ++ [.block [sth .x15 kG]] ++ eqMask aR1 ++
  [.block [ldh .x3 kV, .lsr .x .x3 .x3 60, movi .x4 1, .subs .x .x3 .x3 .x4, movi .x7 0, .subImm .x .x8 .x7 1,
    .csel .x .x6 .x8 .x7, ldh .x5 kG, .logic .orr .x .x15 .x15 .x5, .logic .and .x .x15 .x15 .x6,
    .logic .eor .x .x6 .x6 .x8, ldh .x4 kFlag, .logic .and .x .x4 .x4 .x6, .logic .orr .x .x4 .x4 .x15,
    sth .x4 kFlag, ldh .x3 kV, .lsl .x .x3 .x3 4, sth .x3 kV, ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits]]

/-- A squaring after the windows: `y := y²`, the flag or'ed with `y = −1`
under the mask of `σ > j` (from `l`). -/
def mrLast (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : List (Prog isa) :=
  [mul aY aY aY] ++ eqMask aRm1 ++
  [.block (ws ++ base aE .x16 ++ [.lsl .x .x5 .x12 3, .add .x .x16 .x16 .x5, ld .x3 .x16] ++ ldK j ++
    [.logic .and .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4, movi .x7 0, .subImm .x .x8 .x7 1,
      .csel .x .x6 .x8 .x7, .logic .and .x .x15 .x15 .x6, ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x15,
      sth .x4 kFlag])]

/-- The flag over the windows of `E`, its words from the top, 16 windows
each, then three more squarings: `mrIteration`'s result. -/
def mrExpLoop (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [ldh .x3 sW, sth .x3 kWords, movi .x3 0, sth .x3 kFlag],
  .loop (seqs [
    .block (ws ++ base aE .x16 ++ [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, .lsl .x .x5 .x3 3,
      .add .x .x4 .x16 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 16, sth .x6 kBits]),
    .loop (seqs (mrWin mul)) (.nonzero .x .x3),
    .block [ldh .x3 kWords]]) (.nonzero .x .x3)] ++
  mrLast mul 1 ++ mrLast mul 2 ++ mrLast mul 3

/-- `[a]` into the entry whose base is in `kV` (`w` words). -/
def toEnt (a : Nat) : List (Prog isa) := [.block (ws ++ base a .x16 ++ [ldh .x17 kV]), copyWords]

/-- `kV := kV + 8 (w + 2)`: the next entry. -/
def nextEnt : List Instr := [ldh .x3 kV, ldh .x4 sStride, .add .x .x3 .x3 .x4, sth .x3 kV]

/-- The table, from `b R mod c` in `aXm`: `T_0 := R mod c`, `T_1 := b R mod c`
and `y := T_1`; then `y := y T_1` into each entry from 2 to 15 (the entry's
base in `kV`, the count in `kBits`); then `y := 1`. -/
def tabBuild (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [.block (ws ++ base aT0 .x3 ++ [sth .x3 kV, movi .x3 14, sth .x3 kBits])] ++ toEnt aR1 ++ [.block nextEnt] ++
  toEnt aXm ++ [.block nextEnt, copyA aY aXm,
  .loop (seqs ([mul aY aY aXm] ++ toEnt aY ++
    [.block (nextEnt ++ [ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits])])) (.nonzero .x .x3),
  copyA aY aR1]

/-- One round from a prepared Montgomery witness: table and fixed windows. -/
def preparedRound (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  tabBuild mul ++ mrExpLoop mul

end VG.Impl.RsaKeyGen.AArch64.Candidate
