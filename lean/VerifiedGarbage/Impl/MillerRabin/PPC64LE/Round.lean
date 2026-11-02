module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-!
# The shared Miller–Rabin round on PPC64LE

`vg_miller_rabin_round(ws = r3, ws_len = r4)`, from a prepared workspace in
the compact representation (`Proof.MillerRabin.Round.compact`): the candidate `c`
in array 0, the witness `b R mod c` in array 5, `R mod c` in array 9,
`c − R mod c` in array 10, the exponent `E = (c − 1) / 2^σ` in array 27,
followed by `l = 2^(v₂(c − 1) mod 64)`; the table of `T_j = b^j R mod c`
goes in arrays 11 to 26, and `y` in array 6.

The algorithm is the AArch64 round's (`Impl/MillerRabin/AArch64/Core.lean`,
proven against `Proof/RsaKeyGen/MrWindow.lean`): the table; then for each
window of four bits of `E` from its top, four squarings, each or'ing the
flag `P` with `y = −1`, then `y := y T_d` and, if `d ≠ 0`, `P := y = 1 ∨
y = −1`; then three more squarings, the flag or'ed with `y = −1` under the
mask of `σ > j`. `P` is a mask: nothing branches on a secret value, and
`T_d` is selected by a scan of the whole table.

The Montgomery multiplications are `PublicChecked.montOp`'s, inline
(`MontMul.lean`), with array 0 at `r10`, the arrays' size in `r29`, `2 w`
in `r11` and `-c⁻¹ mod 2³²` (the low half of the header's word 7) in `r12`.
Copies and the selection are `MontMul.selectAcc64`'s masked copies of 64-bit
words, into a different array: `T_d` is selected into array 3 and array 5 in
turn. Comparisons `or` the `xor`s of the words, and the borrow of `0 −` that
`or` (`subfc`) is the mask.

Registers kept across the multiplications: `r23` the flag, `r24` the word
of `E` being scanned, `r25` its address, `r26` the words left, `r27` the
windows left, `r28` the digit, `r30` a table index, `r31` the working
space, `r21` the buffer on the stack where the nonvolatile registers are
saved.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

/-! ## The arrays -/

def aY : Nat := 6
def aW : Nat := 5
def aT : Nat := 3
def aOne : Nat := 9
def aMinus : Nat := 10
def aTab : Nat := 11
def aE : Nat := 27

/-! ## Saving the nonvolatile registers -/

/-- The nonvolatile registers saved, `r21` (which keeps the buffer's address)
last. -/
def saved (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31,
    .r21].getD i .r14

/-- Save them in the buffer at `r5`, and keep its address in `r21`. -/
def save : List Instr :=
  (List.range 18).flatMap (fun i => [.store .d (saved i) .r5 (8 * i)]) ++ [.addi .r21 .r5 0]

/-- Restore them, through `r21`, which is restored last. -/
def restore : List Instr :=
  (List.range 17).flatMap (fun i => [.load .d (saved i) .r21 (8 * i)]) ++ [.load .d .r21 .r21 136]

/-- The working space in `r31`, array 0 at `r10`, `2 w` in `r11`, the
arrays' size `8 (w + 2)` in `r29` and `-c⁻¹ mod 2³²` in `r12`. -/
def setup : List Instr :=
  [.addi .r31 .r3 0, .addi .r10 .r3 hdrBytes, .load .d .r11 .r3 (8 * sW), .lsl .r29 .r11 3,
    .addi .r29 .r29 16, .lsl .r11 .r11 1, .load .w .r12 .r3 (8 * sMinv)]

/-! ## Copies, selections, comparisons -/

/-- `[o] := r20 ? [a] : [t]` (`selectAcc64`), for `o` other than `a` and `t`. -/
def sel (o a t : Nat) : Prog isa :=
  .seq (.block (base .r8 a ++ base .r9 t ++ base .r5 o)) selectAcc64

/-- `r20 :=` all ones. -/
def ones : List Instr := [.li .r20 0, .subi .r20 .r20 1]

/-- `[o] := [a]`. -/
def copy (o a : Nat) : Prog isa := .seq (.block ones) (sel o a a)

/-- `r8 :=` the base of table entry `r30`: array `11 + r30`. -/
def entry : List Instr := [.addi .r8 .r30 aTab, .mul .r8 .r8 .r29, .add .r8 .r8 .r10]

/-- Table entry `r30 := [a]`. -/
def toEntry (a : Nat) : Prog isa :=
  .seq (.block (ones ++ entry ++ [.addi .r5 .r8 0] ++ base .r8 a ++ base .r9 a)) selectAcc64

/-- `d := ` all ones if the `w` words of arrays `a` and `b` are equal,
else 0: the `or` of their `xor`s is zero, which `0 −` it does not borrow. -/
def eqMask (d : Reg) (a b : Nat) : Prog isa :=
  .seq (.block (base .r14 a ++ base .r15 b ++ [.lsr .d .r17 .r11 1, .li .r3 0]))
    (.seq (countLoop .r17 [.load .d .r0 .r14 0, .load .d .r4 .r15 0, .logic .xor .r0 .r0 .r4,
        .logic .or .r3 .r3 .r0, .addi .r14 .r14 8, .addi .r15 .r15 8])
      (.block [.li .r0 0, .subc .r3 .r0 .r3, .addze .r3 .r0, .sub d .r0 .r3]))

/-! ## The table -/

/-- `T_0 := R mod c`, `T_1 := y := b R mod c`, then `y := y b` into each
entry from 2 to 15, then `y := R mod c`. -/
def table : Prog isa :=
  .seq (.block [.li .r30 0]) (.seq (toEntry aOne) (.seq (.block [.li .r30 1]) (.seq (toEntry aW)
    (.seq (copy aY aW) (.seq (.block [.li .r30 2])
      (.seq (.loop (.seq (montOp aY aY aW) (.seq (toEntry aY) (.block [.addi .r30 .r30 1, .subi .r4 .r30 16])))
          (.nonzero .d .r4))
        (copy aY aOne)))))))

/-! ## A window -/

/-- `y := y²`, the flag or'ed with `y = −1`. -/
def square : Prog isa :=
  .seq (montOp aY aY aY) (.seq (eqMask .r20 aY aMinus) (.block [.logic .or .r23 .r23 .r20]))

/-- `r20 :=` all ones if `r30 = r28`, else 0 (both below 16). -/
def isDigit : List Instr :=
  [.logic .xor .r3 .r30 .r28, .subi .r3 .r3 1, .lsr .d .r3 .r3 63, .li .r0 0, .sub .r20 .r0 .r3]

/-- `T_d` into array 5, `d` in `r28`: for each pair of entries `j`, `j + 1`,
array 3 `:= j = d ? T_j : [5]`, then array 5 `:= j + 1 = d ? T_(j+1) : [3]`. -/
def select : Prog isa :=
  .seq (.block [.li .r30 0])
    (.loop (.seq (.block (isDigit ++ entry ++ base .r9 aW ++ base .r5 aT)) (.seq selectAcc64
      (.seq (.block ([.addi .r30 .r30 1] ++ isDigit ++ entry ++ base .r9 aT ++ base .r5 aW)) (.seq selectAcc64
        (.block [.addi .r30 .r30 1, .subi .r4 .r30 16]))))) (.nonzero .d .r4))

/-- After `y := y T_d`: the flag `P := d ≠ 0 ? (y = 1 ∨ y = −1) : P`. -/
def update : Prog isa :=
  .seq (eqMask .r20 aY aMinus) (.seq (eqMask .r19 aY aOne)
    (.block [.logic .or .r20 .r20 .r19, .li .r0 0, .sub .r3 .r0 .r28, .lsr .d .r3 .r3 63, .sub .r3 .r0 .r3,
      .logic .xor .r20 .r20 .r23, .logic .and .r20 .r20 .r3, .logic .xor .r23 .r23 .r20]))

/-- One window, its digit at the top of `r24`: four squarings, `y := y T_d`,
the flag, then `r24 := r24 << 4`. -/
def window : Prog isa :=
  .seq square (.seq square (.seq square (.seq square
    (.seq (.block [.lsr .d .r28 .r24 60]) (.seq select (.seq (montOp aY aY aW)
      (.seq update (.block [.lsl .r24 .r24 4]))))))))

/-! ## The exponent -/

/-- The windows of `E`, its words from the top, 16 windows each. -/
def windows : Prog isa :=
  .seq (.block ([.li .r23 0, .lsr .d .r26 .r11 1] ++ base .r25 aE ++ [.lsl .r0 .r26 3, .add .r25 .r25 .r0]))
    (.loop (.seq (.block [.subi .r25 .r25 8, .load .d .r24 .r25 0, .li .r27 16])
        (.seq (.loop (.seq window (.block [.subi .r27 .r27 1])) (.nonzero .d .r27)) (.block [.subi .r26 .r26 1])))
      (.nonzero .d .r26))

/-- `r4 := k`, a 64-bit constant whose four 16-bit halves are all `h`. -/
def repeat16 (h : BitVec 16) : List Instr :=
  [.lis .r4 h, .ori .r4 .r4 h, .lsl .r4 .r4 32, .oris .r4 .r4 h, .ori .r4 .r4 h]

/-- The mask of `σ > j`: `l & K ≠ 0` for `l` the word after `E`, `K`'s
nibbles `0xD`, `0x9` or `0x1` for `j = 1, 2, 3`. -/
def sigK (j : Nat) : BitVec 16 := if j = 1 then 0xDDDD else if j = 2 then 0x9999 else 0x1111

/-- A squaring after the windows: `y := y²`, the flag or'ed with `y = −1`
under the mask of `σ > j`. -/
def last (j : Nat) : Prog isa :=
  .seq (montOp aY aY aY) (.seq (eqMask .r20 aY aMinus)
    (.block (base .r3 aE ++ [.lsr .d .r0 .r11 1, .lsl .r0 .r0 3, .add .r3 .r3 .r0, .load .d .r3 .r3 0] ++
      repeat16 (sigK j) ++ [.logic .and .r3 .r3 .r4, .lsr .d .r4 .r3 1, .li .r0 1, .logic .and .r0 .r3 .r0,
        .logic .or .r3 .r4 .r0, .li .r0 0, .sub .r3 .r0 .r3, .lsr .d .r3 .r3 63, .sub .r3 .r0 .r3,
        .logic .and .r20 .r20 .r3, .logic .or .r23 .r23 .r20])))

/-- The round: the table, the windows, the three squarings; the flag's low
bit returned. -/
def core : Prog isa :=
  .seq table (.seq windows (.seq (last 1) (.seq (last 2) (last 3))))

def round : Prog isa :=
  .seq (.block (save ++ setup)) (.seq core (.block ([.li .r3 1, .logic .and .r3 .r3 .r23] ++ restore)))

end VG.Impl.MillerRabin.PPC64LE
