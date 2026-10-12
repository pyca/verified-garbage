module

public import VerifiedGarbage.Impl.Rsa.AArch64
public import VerifiedGarbage.Impl.Bignum.CrtLayout

/-!
# RSA with the CRT private key on AArch64

`vg_rsa_private_crt(out, out_len, n, n_len, input, input_len, p, p_len, q,
q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the
first eight arguments in `x0`–`x7`, the others on the stack (AAPCS64).

The computation is x86-64's (`Impl/Rsa/X86_64/Crt.lean`), in the same
layout (`Impl/Bignum/CrtLayout.lean`): three workspaces, `n`'s at
`scratch`, then `p`'s and `q`'s (`max(2, ⌈len / 8⌉)` words each), each
followed by the 16 entries of its exponentiation's table. The code runs in
one at a time, its base in `x0`; the headers of `p`'s and `q`'s link back
to `n`'s.

1. `n` is checked as `vg_rsa_public_checked` checks it (it is public, so
   the code branches on it), and loaded with the input `c`, the mask of
   `c < n`, `-n⁻¹`, `R² mod n`, the number 1 and `c` in Montgomery form.
2. `p`, `q` and `qInv` are loaded, and the mask of `c < n`, `p q = n` and
   `qInv < p` computed; where it is clear, `p` and `q` are replaced by 3,
   so that what follows computes with valid values either way, and the
   result is masked at the end.
3. For `X = q`, then `X = p`: `c R_X mod X` (`R_X = 2^(64 w_X)`) without
   `R_X² mod X`, as `X` divides `n`: `G = 2^E mod n` for
   `E = 64 w_X (K + 1)` and `K = ⌈w / w_X⌉`, then `x G mod n` reduced by
   `K` Montgomery steps mod `X` (`redc`): `x R_X mod X`.
4. `m_X = c^d_X mod X` by a fixed window of 4 bits, with a table of the 16
   powers after the prime's arrays, each entry read by a masked selection
   from all of them (`tabSelect`); `h = (m_p - m_q) qInv mod p` and
   `m = m_q + q h`, written out masked.

Every loop counts down a register with `cbnz`, or tests a value computed
into a register, and every comparison's carry is made a register's value by
`csel`: the model branches only on whether a register is zero. The code
writes no callee-saved register, and uses no stack.
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.Crt

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt
open VG.Impl.Bignum.Public hiding sI sBit sV
open VG.Impl.Rsa.AArch64

/-- `t = [b + 8 i]`, header slot `i` of the workspace at `b`. -/
def ldw (t b : Reg) (i : Nat) : Instr := .ldr .x t b (8 * i)

/-- Header slot `i` of the workspace at `b` `= t`. -/
def stw (t b : Reg) (i : Nat) : Instr := .str .x t b (8 * i)

/-! ## Entry -/

/-- The arguments in the header at `scratch` (the ninth stack argument),
whose base goes in `x0`. -/
def entry : List Instr :=
  [.ldrSp .x8 64, stw .x0 .x8 sOut, stw .x2 .x8 sN, stw .x3 .x8 sK, stw .x4 .x8 sIn, stw .x6 .x8 sP,
    stw .x7 .x8 sPlen, .ldrSp .x9 0, stw .x9 .x8 sQ, .ldrSp .x9 8, stw .x9 .x8 sQlen, .ldrSp .x9 16,
    stw .x9 .x8 sDp, .ldrSp .x9 32, stw .x9 .x8 sDq, .ldrSp .x9 48, stw .x9 .x8 sQinv, mov .x0 .x8]

/-! ## `n`'s workspace -/

/-- `x4 := 0 - 1`, and `x15 :=` all ones on a borrow (the carry clear), 0
otherwise; `x7 = 0`. -/
def borrowMask : List Instr := [.subImm .x .x4 .x7 1, .csel .x .x15 .x7 .x4]

/-- `n` and `-n⁻¹` (`pcLoad`); the input `c`; the mask of `c < n`; the number
1; `R² mod n` (as `vg_rsa_public_precompute` computes it) and `c R mod n`. -/
def nSetup (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  pcLoad ++ [
  .block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)],
  loadBE,
  .block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block (borrowMask ++ [sth .x15 sMask, ldh .x12 sW, movi .x9 1, movi .x13 0]),
  setWord aOne] ++
  r2Steps mul ++ [mul aXm aX aR2]

/-! ## The prime workspaces -/

/-- `x4 := ` the end of the arrays of the workspace at `x5`: its last
array's base plus `8 (w + 2)` (in `x6`). -/
def wsEnd : List Instr :=
  [ldw .x4 .x5 (sArr aOne), ldw .x6 .x5 sW, .addImm .x .x6 .x6 2, .lsl .x .x6 .x6 3, .add .x .x4 .x4 .x6]

/-- `x4 := ` the end of a prime's workspace at `x5`: its arrays, then the 16
entries of the window's table (`8 (w + 2)` bytes each). -/
def wsEndT : List Instr := wsEnd ++ ([.lsl .x .x6 .x6 4, .add .x .x4 .x4 .x6] : List Instr)

/-- A workspace at `x4` (its base stored in slot `slotWs`) for a number of
the byte length in slot `slotLen`: `w = max(2, ⌈len / 8⌉)`, its arrays'
bases, and its link to `n`'s; `x0` stays `n`'s. -/
def wsNew (slotWs slotLen : Nat) : List Instr :=
  [sth .x4 slotWs, ldh .x12 slotLen, .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3, movi .x5 2,
    .subs .x .x6 .x12 .x5, .csel .x .x12 .x12 .x5, mov .x1 .x0, mov .x0 .x4, sth .x1 sLink, sth .x12 sW] ++
  setBases ++ [mov .x0 .x1]

/-- `[j] := 0` in the current workspace (`w + 2` words). -/
def zeroArr (j : Nat) : Prog isa :=
  .seq (.block [ldh .x8 (sArr j), ldh .x12 sW, movi .x7 0]) zeroAcc

/-- In a prime workspace: `[j] := ` the number of the bytes whose pointer and
length are in `n`'s header slots `slotPtr` and `slotLen`. -/
def loadArr (j slotPtr slotLen : Nat) : List (Prog isa) := [
  zeroArr j,
  .block [ldh .x5 sLink, ldw .x1 .x5 slotPtr, ldw .x2 .x5 slotLen, ldh .x8 (sArr j)],
  loadBE]

/-- Into `p`'s and `q`'s workspaces, from `n`'s, and back. -/
def enterP : Instr := ldh .x0 sWsP
def enterQ : Instr := ldh .x0 sWsQ
def leave : Instr := ldh .x0 sLink

/-- The workspaces, `p`, `q` and `qInv` (into `p`'s chunk array). -/
def primesSetup : List (Prog isa) :=
  [.block ([mov .x5 .x0] ++ wsEnd), .block (wsNew sWsP sPlen), .block ([ldh .x5 sWsP] ++ wsEndT),
    .block (wsNew sWsQ sQlen), .block [enterP]] ++
  loadArr aN sP sPlen ++ loadArr aChunk sQinv sPlen ++ [.block [leave, enterQ]] ++
  loadArr aN sQ sQlen ++ [.block [leave]]

/-! ## The checks -/

/-- `acc := 0` over `2 w + 2` words from `n`'s accumulator. -/
def zeroAccs : List (Prog isa) :=
  [.block [ldh .x16 (sArr aAcc), ldh .x12 sW, movi .x7 0, .add .x .x14 .x12 .x12, .addImm .x .x14 .x14 2],
    countLoop .x14 [st .x7 .x16, next .x16]]

/-- `acc += [x11] [x9]`: rows `acc[i ..] += [x11]_i [x9]` (`x12` words, at
`x8 = acc + 8 i`) for `x13` words of `[x11]`; `x7 = 0`. -/
def mulRows : Prog isa :=
  .loop (.seq (.block [ld .x1 .x11, next .x11]) (.seq mulAddRow (.block [next .x8, .subImm .x .x13 .x13 1])))
    (.nonzero .x .x13)

/-- `p q` into `n`'s accumulators. -/
def pqProduct : List (Prog isa) := zeroAccs ++ [
  .block [ldh .x5 sWsP, ldw .x11 .x5 (sArr aN), ldw .x13 .x5 sW, ldh .x5 sWsQ, ldw .x9 .x5 (sArr aN),
    ldw .x12 .x5 sW, ldh .x8 (sArr aAcc), movi .x7 0],
  mulRows]

/-- The mask of `p q = n`, and'ed into `sMask`: the OR of the words of the
product's `XOR` with `n` over `w` words and of its words `w` to `2 w + 1`,
then all ones if it is zero (no borrow from it minus 1). -/
def eqCheck : List (Prog isa) := [
  .block [ldh .x12 sW, ldh .x16 (sArr aAcc), ldh .x17 (sArr aN), movi .x9 0, mov .x14 .x12],
  countLoop .x14 [ld .x3 .x16, ld .x4 .x17, .logic .eor .x .x3 .x3 .x4, .logic .orr .x .x9 .x9 .x3, next .x16,
    next .x17],
  .block [.addImm .x .x14 .x12 2],
  countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16],
  .block ([movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask ++
    [ldh .x3 sMask, .logic .and .x .x15 .x15 .x3, sth .x15 sMask])]

/-- In `p`'s workspace: the mask of `qInv < p`, and'ed into `n`'s `sMask`. -/
def qinvCheck : List (Prog isa) := [
  .block [ldh .x12 sW, ldh .x16 (sArr aChunk), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12,
    .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block (borrowMask ++ [ldh .x5 sLink, ldw .x3 .x5 sMask, .logic .and .x .x15 .x15 .x3, stw .x15 .x5 sMask])]

/-- `[j] &= sMaskX` over `w` words. -/
def maskArr (j : Nat) : List (Prog isa) := [
  .block [ldh .x15 sMaskX, ldh .x12 sW, ldh .x16 (sArr j), mov .x14 .x12],
  countLoop .x14 [ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x16, next .x16]]

/-- In a prime workspace: the mask from `n`'s; `X := mask ? X : 3` (its low
word or'ed with `3 & ~mask`); `-X⁻¹`; the number 1. -/
def primeFix : List (Prog isa) :=
  [.block [ldh .x5 sLink, ldw .x5 .x5 sMask, sth .x5 sMaskX]] ++
  maskArr aN ++
  [.block ([movi .x4 3, .logic .and .x .x5 .x15 .x4, .logic .eor .x .x5 .x5 .x4, ldh .x16 (sArr aN), ld .x3 .x16,
      .logic .orr .x .x3 .x3 .x5, st .x3 .x16] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
    setWord aOne]

/-- The checks and the fixes. -/
def checks : List (Prog isa) :=
  pqProduct ++ eqCheck ++ [.block [enterP]] ++ qinvCheck ++ primeFix ++ [.block [leave, enterQ]] ++ primeFix ++
  [.block [leave]]

/-! ## Arithmetic modulo a prime -/

/-- `[o] = [a] + [b] mod m` for `[a], [b] < m`: the sum into the
accumulator (`w + 1` words, a chain of `adcs` from the carry clear), then
the subtraction of `m` selected as in `montMul`. -/
def addMod (o a b : Nat) : Prog isa :=
  .seq (.block [ldh .x9 (sArr a), ldh .x17 (sArr b), ldh .x10 (sArr aN), ldh .x8 (sArr aAcc), ldh .x6 (sArr aTmp),
      ldh .x5 (sArr o), ldh .x12 sW, movi .x7 0, mov .x16 .x8, mov .x14 .x12, .adds .x .x3 .x7 .x7])
    (.seq (countLoop .x14 [ld .x3 .x9, ld .x4 .x17, .adcs .x .x3 .x3 .x4, st .x3 .x16, next .x9, next .x17,
      next .x16])
    (.seq (.block [.adc .x .x3 .x7 .x7, st .x3 .x16])
    (.seq subMod selectAcc)))

/-- `[o] = [a] - [b] mod m` for `[a], [b] < m`: the difference into the
accumulator (a chain of `sbcs` from the carry set), then `m` added under the
mask of its borrow. -/
def subModArr (o a b : Nat) : List (Prog isa) := [
  .block [ldh .x16 (sArr a), ldh .x17 (sArr b), ldh .x13 (sArr aAcc), ldh .x12 sW, movi .x7 0, mov .x14 .x12,
    .subs .x .x3 .x7 .x7],
  countLoop .x14 [ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, st .x3 .x13, next .x16, next .x17, next .x13],
  .block (borrowMask ++ [ldh .x10 (sArr aN), ldh .x8 (sArr aAcc), ldh .x5 (sArr o), mov .x14 .x12,
    .adds .x .x3 .x7 .x7]),
  countLoop .x14 [ld .x3 .x10, .logic .and .x .x3 .x3 .x15, ld .x4 .x8, .adcs .x .x3 .x3 .x4, st .x3 .x5,
    next .x10, next .x8, next .x5]]

/-- `[o] := [a]` over `w` words. -/
def copyArr (o a : Nat) : List (Prog isa) :=
  [.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 (sArr o)], copyWords]

/-- In a prime workspace: `[aXc] := x R_X^(-K) mod X` for the `w_n` words at
`n`'s array `j` (`x = Σ x_k R_X^k`, chunks of `w_X` words): `acc := 0`;
for each chunk, `acc := acc R_X⁻¹ + x_k R_X⁻¹ mod X`. A chunk is the next
`min(rem, w_X)` words, which `copyWords` leaves its source pointer past. -/
def redc (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : List (Prog isa) := [
  zeroArr aXc,
  .block [ldh .x5 sLink, ldw .x3 .x5 (sArr j), sth .x3 sSrc, ldw .x3 .x5 sW, sth .x3 sRem],
  .loop (seqs [
    zeroArr aChunk,
    .block [ldh .x3 sRem, ldh .x12 sW, .subs .x .x4 .x3 .x12, .csel .x .x12 .x12 .x3, ldh .x16 sSrc,
      ldh .x17 (sArr aChunk)],
    copyWords,
    .block [sth .x16 sSrc, ldh .x3 sRem, .sub .x .x3 .x3 .x12, sth .x3 sRem],
    mul aXc aXc aOne,
    mul aT aChunk aOne,
    addMod aXc aXc aT,
    .block [ldh .x3 sRem]]) (.nonzero .x .x3)]

/-- In `n`'s workspace: `[aY] := G = 2^E mod n` for `E = 64 w_X (K + 1)`,
`K = ⌈w / w_X⌉`, the prime workspace's base in slot `slotWs`: `D = E - 64 w`
(`x3` steps up by `w_X` while below `w`, into `K w_X`), then `Y = R mod n`
and for each bit of `D` from the top, `Y := Y² R⁻¹` and doubled if the bit
is set: `Y = 2^D R`. -/
def gPow (mul : Nat → Nat → Nat → Prog isa) (slotWs : Nat) : List (Prog isa) := [
  .block [ldh .x5 slotWs, ldw .x5 .x5 sW, ldh .x12 sW, movi .x3 0, movi .x7 0, movi .x8 1],
  .loop (.block [.add .x .x3 .x3 .x5, .subs .x .x4 .x3 .x12, .csel .x .x4 .x7 .x8]) (.nonzero .x .x4),
  .block [.add .x .x3 .x3 .x5, .sub .x .x3 .x3 .x12, .lsl .x .x3 .x3 6, sth .x3 sD],
  topBit,
  .block [sth .x9 sCnt],
  mul aY aR2 aOne,
  .loop (seqs [
    mul aY aY aY,
    .block [ldh .x3 sD, ldh .x4 sCnt, .logic .and .x .x3 .x3 .x4],
    .ite (.nonzero .x .x3) (double aN aAcc aTmp aY) (.block []),
    .block [ldh .x3 sCnt, .lsr .x .x3 .x3 1, sth .x3 sCnt]]) (.nonzero .x .x3)]

/-! ## The exponentiation

By a fixed window of 4 bits: `Y := Y¹⁶ T_v` for each 4 bits `v` of the
exponent, from its top, with the table `T_i = x^i` in Montgomery form
(`T_0 = Y`, which is 1 in Montgomery form). The entry is read by a masked
selection from every entry, so the addresses do not depend on `v`. -/

/-- `[sEnt] += 8 (w + 2)`: the next entry. -/
def nextEnt : Prog isa :=
  .block [ldh .x3 sEnt, ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4, sth .x3 sEnt]

/-- `[sEnt] := [a]` over `w` words. -/
def toEnt (a : Nat) : List (Prog isa) :=
  [.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 sEnt], copyWords]

/-- The table, after the workspace's last array: `T_0 := Y`, `T_1 := [aXc]`,
and `T_i := T_(i-1) [aXc] R⁻¹` (in `aT`) for `i` from 2 to 15. -/
def tabBuild (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [.block [ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
    sth .x3 sTab, sth .x3 sEnt]] ++
  toEnt aY ++ [nextEnt] ++ toEnt aXc ++ copyArr aT aXc ++
  [.block [movi .x3 14, sth .x3 sBit],
    .loop (seqs ([mul aT aT aXc, nextEnt] ++ toEnt aT ++
      [.block [ldh .x3 sBit, .subImm .x .x3 .x3 1, sth .x3 sBit]])) (.nonzero .x .x3)]

/-- `[x17] := x15 ? [x16] : [x17]` over `x14` words, `x15` a mask: each word
`T ^ ((T ^ E) & mask)`. -/
def selLoop : Prog isa :=
  countLoop .x14 [ld .x3 .x16, ld .x4 .x17, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x3 .x3 .x15,
    .logic .eor .x .x4 .x4 .x3, st .x4 .x17, next .x16, next .x17]

/-- `[aT] := T_v`, `v` in `sNib`: for each entry `j`, `[aT] := T_j` under the
mask of `j = v` (all ones iff `j ⊕ v - 1` borrows). -/
def tabSelect : List (Prog isa) :=
  [.block [ldh .x3 sTab, sth .x3 sEnt, movi .x3 0, sth .x3 sJ],
    .loop (seqs [
      .block ([ldh .x3 sJ, ldh .x4 sNib, .logic .eor .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4,
        movi .x7 0] ++ borrowMask ++ [ldh .x12 sW, ldh .x16 sEnt, ldh .x17 (sArr aT), mov .x14 .x12]),
      selLoop,
      nextEnt,
      .block [ldh .x3 sJ, .addImm .x .x3 .x3 1, sth .x3 sJ, .subImm .x .x4 .x3 16]]) (.nonzero .x .x4)]

/-- One window: `Y := Y¹⁶ T_v R⁻¹` for `v` the top 4 bits of the byte in
`sV`, which moves up 4 bits. -/
def expWin (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY,
    .block [ldh .x3 sV, .lsl .x .x4 .x3 4, sth .x4 sV, .lsr .x .x3 .x3 4, movi .x4 15, .logic .and .x .x3 .x3 .x4,
      sth .x3 sNib]] ++
  tabSelect ++
  [mul aY aY aT,
    .block [ldh .x3 sBit, .subImm .x .x3 .x3 1, sth .x3 sBit]]

/-- `Y := Y^d` (`Y` 1 and `[aXc]` in Montgomery form) for the exponent whose
pointer and length are in `n`'s header slots `slotPtr` and `slotLen`, its
bytes most significant first, two windows a byte. -/
def expLoop (mul : Nat → Nat → Nat → Prog isa) (slotPtr slotLen : Nat) : List (Prog isa) := [
  .block [ldh .x5 sLink, ldw .x3 .x5 slotPtr, sth .x3 sExp, ldw .x3 .x5 slotLen, sth .x3 sExpLen, movi .x3 0,
    sth .x3 sI]] ++
  tabBuild mul ++ [
  .loop (seqs [
    .block [ldh .x3 sExp, ldh .x4 sI, .add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 sV, movi .x3 2, sth .x3 sBit],
    .loop (seqs (expWin mul)) (.nonzero .x .x3),
    .block [ldh .x3 sI, .addImm .x .x3 .x3 1, sth .x3 sI, ldh .x4 sExpLen, .sub .x .x3 .x4 .x3]]) (.nonzero .x .x3)]

/-! ## The primes -/

/-- `q`: `m_q = c^dQ mod q` into `q`'s `aY`. -/
def qPhase (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  gPow mul sWsQ ++ [.block [enterQ]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], mul aY aXm aY,
    .block [enterQ]] ++ redc mul aY ++ expLoop mul sDq sQlen ++ [mul aY aY aOne, .block [leave]]

/-- `p`: `m_p R_p` into `p`'s `aY`, `m_q R_p` into its `aXc`, their
difference into `aT`, `qInv` again (masked) into its chunk array, and
`h = (m_p - m_q) qInv mod p` into its `aY`. -/
def pPhase (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  gPow mul sWsP ++ [.block [enterP]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], zeroArr aX,
    .block [ldh .x5 sWsQ, ldw .x16 .x5 (sArr aY), ldw .x12 .x5 sW, ldh .x17 (sArr aX)],
    copyWords, mul aX aX aR2, mul aX aX aY, mul aY aXm aY, .block [enterP]] ++
  redc mul aY ++ expLoop mul sDp sPlen ++ [.block [leave]] ++ [.block [enterP]] ++ redc mul aX ++
  subModArr aT aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul aY aT aChunk, .block [leave]]

/-! ## The result -/

/-- `m = m_q + q h` into `n`'s accumulators, written out masked, and the
mask's low bit returned. -/
def finish : List (Prog isa) := zeroAccs ++ [
  .block [ldh .x5 sWsQ, ldw .x16 .x5 (sArr aY), ldw .x12 .x5 sW, ldh .x17 (sArr aAcc)],
  copyWords,
  .block [ldh .x5 sWsP, ldw .x11 .x5 (sArr aY), ldw .x13 .x5 sW, ldh .x5 sWsQ, ldw .x9 .x5 (sArr aN),
    ldw .x12 .x5 sW, ldh .x8 (sArr aAcc), movi .x7 0],
  mulRows,
  .block [ldh .x8 (sArr aAcc), ldh .x1 sOut, ldh .x9 sK, .add .x .x1 .x1 .x9, ldh .x15 sMask],
  storeBE,
  .block [ldh .x0 sMask, movi .x3 1, .logic .and .x .x0 .x0 .x3]]

/-- The computation, once `n` is known valid. -/
def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetup mul ++ primesSetup ++ checks ++ qPhase mul ++ pPhase mul ++ finish)

/-- `vg_rsa_private_crt`: `n` checked as the public-key operation checks it
(`invalid`, on `x2` and `x3`, still `n` and `n_len`). -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (entry ++ invalid)) (.ite (.zero .x .x9) Precomputed.fail (main mul))

end VG.Impl.Rsa.AArch64.Crt
