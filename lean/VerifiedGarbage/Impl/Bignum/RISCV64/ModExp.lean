module

public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked
public import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr

/-!
# Modular exponentiation by a secret exponent on RISC-V: four-bit windows

`powWin`: `x^d mod m` into array 4, for `x` in array 4 and the exponent `d`'s
`s10 ≥ 1` bytes at `s9`, most significant first, as PPC64LE's
`ModExp.powWin`, in a working space of 24 arrays of the public-key
operation's layout (`PublicChecked.lean`: `a7` array 0's base, `s5` an
array's size, `t0` `w`, `t1` `-m⁻¹ mod 2⁶⁴`): `m` in array 0, `R² mod m` in
array 1, `x` and then the result in array 4, the selected entry in array 5,
the power `a` in array 6, 1 in array 7, and the table `T_j = x^j R mod m` in
arrays `8 + j` for `j < 16`. Arrays 2 and 3 are the Montgomery
multiplications' accumulator and temporary, and together the product of a
squaring (`MontSqr.lean`'s `sqrTail`, with array 5, free between windows, its
temporary).

Each byte of the exponent is two windows: four Montgomery squares of `a`,
then `a := a T_d` for the window's digit `d`, `T_d` selected by a masked scan
of the whole table, so that no address and no branch depends on `d`.

Registers: `s7` the exponent's bits (or, building the table, the entry), `s9`
the exponent's pointer, `s10` its bytes left, `s8` the entry being scanned and
`a1` the digit (`select`); `s4` the selection's mask.
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64.ModExp

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.PublicChecked

/-- `[o] := [a]² R⁻¹ mod m`: `sqrTail` with the bases, the temporary `p`. -/
def sqrOp (o a p : Nat) : Prog isa :=
  .seq (.block (base .a2 o ++ base .a3 a ++ base .a5 2 ++ base .a6 p)) sqrTail

/-- `s4 :=` all ones. -/
def ones : List Instr := [.li .s4 (-1)]

/-- `[o] := [a]`, for `o` other than `a`. -/
def copy (o a : Nat) : Prog isa :=
  .seq (.block (ones ++ base .a5 a ++ base .a6 a ++ base .a2 o)) selectAcc64

/-- `rd :=` the base of table entry `rj`: array `8 + rj`. -/
def entry (rd rj : Reg) : List Instr := [.addi .t2 rj 8, .mul .t2 .t2 .s5, .add rd .t2 .a7]

/-- Table entry `s7 := [6]`. -/
def toEntry : Prog isa :=
  .seq (.block (ones ++ entry .a2 .s7 ++ base .a5 6 ++ base .a6 6)) selectAcc64

/-- The table: `T_0 = R mod m`, `T_1 = x R mod m`, then `a := a T_1` into
each entry from 2 to 15 (`s7` the entry); then `a := T_0`. -/
def table : Prog isa :=
  .seq one (.seq (montOp 8 1 7) (.seq (montOp 9 4 1) (.seq (copy 6 9) (.seq (.block [.li .s7 2])
    (.seq (.loop (.seq (montOp 6 6 9) (.seq toEntry
        (.block [.addi .s7 .s7 1, .addi .t2 .s7 (-16)]))) (.nonzero .t2))
      (copy 6 8))))))

/-- `s4 :=` all ones if `s8 = a1`, else 0 (both below 16). -/
def isDigit : List Instr :=
  [.logic .xor .t2 .s8 .a1, .addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .li .t3 0, .sub .s4 .t3 .t2]

/-- `T_d` into array 5, `d` in `a1`: for each pair of entries `j`, `j + 1`,
array 3 `:= j = d ? T_j : [5]`, then array 5 `:= j + 1 = d ? T_(j+1) : [3]`. -/
def select : Prog isa :=
  .seq (.block [.li .s8 0])
    (.loop (.seq (.block (isDigit ++ entry .a5 .s8 ++ base .a6 5 ++ base .a2 3)) (.seq selectAcc64
      (.seq (.block ([.addi .s8 .s8 1] ++ isDigit ++ entry .a5 .s8 ++ base .a6 3 ++ base .a2 5)) (.seq selectAcc64
        (.block [.addi .s8 .s8 1, .addi .t2 .s8 (-16)]))))) (.nonzero .t2))

/-- One window, its digit at the top of `s7`: four squares, `a := a T_d`,
then `s7 := s7 << 4`. -/
def window : Prog isa :=
  .seq (sqrOp 6 6 5) (.seq (sqrOp 6 6 5) (.seq (sqrOp 6 6 5) (.seq (sqrOp 6 6 5)
    (.seq (.block [.shift .srl .d .a1 .s7 60]) (.seq select (.seq (montOp 6 6 5)
      (.block [.shift .sll .d .s7 .s7 4])))))))

/-- The two windows of the byte at `s9`, `s9` advanced. -/
def byteWin : Prog isa :=
  .seq (.block [.load .b .s7 .s9 0, .shift .sll .d .s7 .s7 56, .addi .s9 .s9 1]) (.seq window window)

/-- `x^d mod m` into array 4, for `d`'s `s10` bytes at `s9`: the table, the
windows of every byte, then out of Montgomery form. -/
def powWin : Prog isa :=
  .seq table (.seq (.loop (.seq byteWin (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10)) (montOp 4 6 7))

end VG.Impl.Bignum.RISCV64.ModExp
