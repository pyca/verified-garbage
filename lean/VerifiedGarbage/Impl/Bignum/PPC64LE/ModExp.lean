module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-!
# Modular exponentiation by a secret exponent on PPC64LE

`powSecret`: `x^d mod m` for an exponent `d` of a public number of bytes,
read most significant first from memory (`r30`, `r31` bytes), whose value is
secret. In the public-key operation's working space (`PublicChecked`): `m` in
array 0, `R² mod m` in array 1, `x` in array 4, with `r10` array 0's base,
`r29` an array's size, `r11` `2 w` and `r12` `-m⁻¹ mod 2³²`; the result in
array 4.

Every bit of every byte is scanned from the top: a Montgomery square and a
Montgomery multiplication by `x R mod m`, the product selected by a mask of
the bit (`PublicChecked.step`). The code is the same for every exponent of
the same length, and nothing branches on its value.
-/

@[expose] public section

namespace VG.Impl.Bignum.PPC64LE.ModExp

open VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

/-- The eight bits of the byte at `r30`, from the top, `r30` advanced. -/
def byteScan : Prog isa :=
  .seq (.block [.lbz .r24 .r30 0, .lsl .r24 .r24 56, .addi .r30 .r30 1, .li .r25 8])
    (.loop (.seq PublicChecked.step (.block [.subi .r25 .r25 1])) (.nonzero .d .r25))

/-- The `r31` bytes from `r30`, each scanned. -/
def scan : Prog isa :=
  .loop (.seq byteScan (.block [.subi .r31 .r31 1])) (.nonzero .d .r31)

/-- `x^d mod m` into array 4: `a := R mod m`, `x R mod m` into array 6, the
scan, then out of Montgomery form. -/
def powSecret : Prog isa :=
  .seq one (.seq (montOp 5 1 7) (.seq (montOp 6 4 1) (.seq scan (montOp 4 5 7))))

/-! ## Four-bit windows

`powWin` computes the same as `powSecret` in a working space of 24 arrays:
`m` in array 0, `R² mod m` in array 1, `x` and then the result in array 4,
the selected entry in array 5, the power `a` in array 6, 1 in array 7, and
the table `T_j = x^j R mod m` in arrays `8 + j` for `j < 16`. Each byte of
the exponent is two windows: four Montgomery squares of `a`, then `a := a
T_d` for the window's digit `d`, `T_d` selected by a masked scan of the
whole table, so that no address depends on `d`. -/

/-- `r20 :=` all ones. -/
def ones : List Instr := [.li .r20 0, .subi .r20 .r20 1]

/-- `[o] := [a]`, for `o` other than `a`. -/
def copy (o a : Nat) : Prog isa :=
  .seq (.block (ones ++ base .r8 a ++ base .r9 a ++ base .r5 o)) selectAcc

/-- `r8 :=` the base of table entry `r19`: array `8 + r19`. -/
def entry : List Instr := [.addi .r8 .r19 8, .mul .r8 .r8 .r29, .add .r8 .r8 .r10]

/-- Table entry `r19 := [6]`. -/
def toEntry : Prog isa :=
  .seq (.block (ones ++ entry ++ [.addi .r5 .r8 0] ++ base .r8 6 ++ base .r9 6)) selectAcc

/-- The table: `T_0 = R mod m`, `T_1 = x R mod m`, then `a := a T_1` into
each entry from 2 to 15 (`r24` the entry); then `a := T_0`. -/
def table : Prog isa :=
  .seq one (.seq (montOp 8 1 7) (.seq (montOp 9 4 1) (.seq (copy 6 9) (.seq (.block [.li .r24 2])
    (.seq (.loop (.seq (montOp 6 6 9) (.seq (.block [.addi .r19 .r24 0]) (.seq toEntry
        (.block [.addi .r24 .r24 1, .subi .r4 .r24 16])))) (.nonzero .d .r4))
      (copy 6 8))))))

/-- `r20 :=` all ones if `r19 = r18`, else 0 (both below 16). -/
def isDigit : List Instr :=
  [.logic .xor .r3 .r19 .r18, .subi .r3 .r3 1, .lsr .d .r3 .r3 63, .li .r0 0, .sub .r20 .r0 .r3]

/-- `T_d` into array 5, `d` in `r18`: for each pair of entries `j`, `j + 1`,
array 3 `:= j = d ? T_j : [5]`, then array 5 `:= j + 1 = d ? T_(j+1) : [3]`. -/
def select : Prog isa :=
  .seq (.block [.li .r19 0])
    (.loop (.seq (.block (isDigit ++ entry ++ base .r9 5 ++ base .r5 3)) (.seq selectAcc
      (.seq (.block ([.addi .r19 .r19 1] ++ isDigit ++ entry ++ base .r9 3 ++ base .r5 5)) (.seq selectAcc
        (.block [.addi .r19 .r19 1, .subi .r4 .r19 16]))))) (.nonzero .d .r4))

/-- One window, its digit at the top of `r24`: four squares, `a := a T_d`,
then `r24 := r24 << 4`. -/
def window : Prog isa :=
  .seq (sqrOp 6 6) (.seq (sqrOp 6 6) (.seq (sqrOp 6 6) (.seq (sqrOp 6 6)
    (.seq (.block [.lsr .d .r18 .r24 60]) (.seq select (.seq (montOp 6 6 5) (.block [.lsl .r24 .r24 4])))))))

/-- The two windows of the byte at `r30`, `r30` advanced. -/
def byteWin : Prog isa :=
  .seq (.block [.lbz .r24 .r30 0, .lsl .r24 .r24 56, .addi .r30 .r30 1]) (.seq window window)

/-- `x^d mod m` into array 4, for `d`'s `r31` bytes at `r30`: the table, the
windows of every byte, then out of Montgomery form. -/
def powWin : Prog isa :=
  .seq table (.seq (.loop (.seq byteWin (.block [.subi .r31 .r31 1])) (.nonzero .d .r31)) (montOp 4 6 7))

end VG.Impl.Bignum.PPC64LE.ModExp
