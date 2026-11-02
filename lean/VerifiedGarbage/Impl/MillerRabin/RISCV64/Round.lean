module

public import VerifiedGarbage.Impl.Bignum.RISCV64.ModExp
public import VerifiedGarbage.Impl.StackScratch.RISCV64

/-!
# The shared Miller–Rabin round on RISC-V

`vg_miller_rabin_round(ws = a0, ws_len = a1)`, from a prepared working space
in the compact representation (`Proof.MillerRabin.Round.compact`), as on
PPC64LE (`Impl/MillerRabin/PPC64LE/Round.lean`): the candidate `c` in array
0, the witness `b R mod c` in array 5, `R mod c` in array 9, `c − R mod c` in
array 10, the exponent `E = (c − 1) / 2^σ` in array 27, followed by `l =
2^(v₂(c − 1) mod 64)`; the table of `T_j = b^j R mod c` goes in arrays 11 to
26, and `y` in array 6.

The algorithm is the AArch64 and PPC64LE rounds' (proven against
`Proof/RsaKeyGen/MrWindow.lean`): the table; then for each window of four
bits of `E` from its top, four squarings, each or'ing the flag `P` with `y =
−1`, then `y := y T_d` and, if `d ≠ 0`, `P := y = 1 ∨ y = −1`; then three
more squarings, the flag or'ed with `y = −1` under the mask of `σ > j`. `P`
is a mask: nothing branches on a secret value, and `T_d` is selected by a
scan of the whole table.

The squarings are `MontSqr.lean`'s `sqrTail` (its product in arrays 2 and 3,
its temporary array 5, which the selection overwrites anyway), the
multiplications `MontMul.lean`'s `tail` (`PublicChecked.montOp`), both
inline, in the public-key operation's registers: `a7` array 0's base, `s5`
the arrays' size, `t0` `w`, `t1` `-c⁻¹ mod 2⁶⁴` (header word 7). Copies and
the selection are `selectAcc64`'s masked copies; a comparison `or`s the
`xor`s of the words, and its mask is `(that = 0) − 1`, by `sltu`.

Registers kept across the multiplications: `s6` the flag, `s7` the word of
`E` being scanned, `s8` its address, `s9` the words left, `s10` the windows
left, `s11` the digit (or, building the table, the entry); `a1` the entry
scanned by the selection. The callee-saved registers are saved in a frame of
`frameBytes` bytes on the stack (`withStackScratch`, its address in `t2`):
the round writes no header word.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.RISCV64

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)
open VG.Impl.Bignum.RISCV64.ModExp (sqrOp copy)

/-! ## The arrays -/

def aY : Nat := 6
def aW : Nat := 5
def aT : Nat := 3
def aOne : Nat := 9
def aMinus : Nat := 10
def aTab : Nat := 11
def aE : Nat := 27

/-! ## Saving the callee-saved registers -/

/-- The frame's size: the twelve callee-saved registers. -/
def frameBytes : Nat := 96

/-- The callee-saved registers, in the order they are saved. -/
def saved (i : Nat) : Reg :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11].getD i .s0

/-- Save them in the frame at `t2`. -/
def save : List Instr := (List.range 12).map (fun i => .store .d (saved i) .t2 (8 * i))

/-- Restore them, from the frame at `sp`. -/
def restore : List Instr := .addSp .t2 0 :: (List.range 12).map (fun i => .load .d (saved i) .t2 (8 * i))

/-- Array 0's base in `a7`, `w` in `t0`, the arrays' size `8 (w + 2)` in `s5`
and `-c⁻¹ mod 2⁶⁴` in `t1`, from the working space at `a0`. -/
def setup : List Instr :=
  [.addi .a7 .a0 hdrBytes, .load .d .t0 .a0 (8 * sW), .shift .sll .d .s5 .t0 3, .addi .s5 .s5 16,
    .load .d .t1 .a0 (8 * sMinv)]

/-! ## Copies, selections, comparisons -/

/-- `rd :=` the base of table entry `rj`: array `11 + rj`, through `t2`. -/
def entry (rd rj : Reg) : List Instr := [.addi .t2 rj aTab, .mul .t2 .t2 .s5, .add rd .t2 .a7]

/-- Table entry `s11 := [a]`. -/
def toEntry (a : Nat) : Prog isa :=
  .seq (.block ([.li .s4 (-1)] ++ entry .a2 .s11 ++ base .a5 a ++ base .a6 a)) selectAcc64

/-- `d :=` all ones if the `w` words of arrays `a` and `b` are equal, else 0:
the `or` of their `xor`s is zero, and `(0 <u that) − 1` the mask. It writes
`t2`–`t5`, `s0`–`s2` and `d`. -/
def eqMask (d : Reg) (a b : Nat) : Prog isa :=
  .seq (.block (base .t3 a ++ base .t4 b ++ [.addi .t5 .t0 0, .li .s0 0]))
    (.seq (countLoop .t5 [.load .d .s1 .t3 0, .load .d .s2 .t4 0, .logic .xor .s1 .s1 .s2,
        .logic .or .s0 .s0 .s1, .addi .t3 .t3 8, .addi .t4 .t4 8])
      (.block [.li .s1 0, .sltu .s1 .s1 .s0, .addi d .s1 (-1)]))

/-! ## The table -/

/-- `T_0 := R mod c`, `T_1 := y := b R mod c`, then `y := y b` into each
entry from 2 to 15, then `y := R mod c`. -/
def table : Prog isa :=
  .seq (.block [.li .s11 0]) (.seq (toEntry aOne) (.seq (.block [.li .s11 1]) (.seq (toEntry aW)
    (.seq (copy aY aW) (.seq (.block [.li .s11 2])
      (.seq (.loop (.seq (montOp aY aY aW) (.seq (toEntry aY) (.block [.addi .s11 .s11 1, .addi .t2 .s11 (-16)])))
          (.nonzero .t2))
        (copy aY aOne)))))))

/-! ## A window -/

/-- `y := y²`, the flag or'ed with `y = −1`. -/
def square : Prog isa :=
  .seq (sqrOp aY aY aW) (.seq (eqMask .a3 aY aMinus) (.block [.logic .or .s6 .s6 .a3]))

/-- `s4 :=` all ones if `a1 = s11`, else 0 (both below 16). -/
def isDigit : List Instr :=
  [.logic .xor .t2 .a1 .s11, .addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .li .t3 0, .sub .s4 .t3 .t2]

/-- `T_d` into array 5, `d` in `s11`: for each pair of entries `j`, `j + 1`,
array 3 `:= j = d ? T_j : [5]`, then array 5 `:= j + 1 = d ? T_(j+1) : [3]`. -/
def select : Prog isa :=
  .seq (.block [.li .a1 0])
    (.loop (.seq (.block (isDigit ++ entry .a5 .a1 ++ base .a6 aW ++ base .a2 aT)) (.seq selectAcc64
      (.seq (.block ([.addi .a1 .a1 1] ++ isDigit ++ entry .a5 .a1 ++ base .a6 aT ++ base .a2 aW)) (.seq selectAcc64
        (.block [.addi .a1 .a1 1, .addi .t2 .a1 (-16)]))))) (.nonzero .t2))

/-- After `y := y T_d`: the flag `P := d ≠ 0 ? (y = 1 ∨ y = −1) : P`. -/
def update : Prog isa :=
  .seq (eqMask .a3 aY aMinus) (.seq (eqMask .a4 aY aOne)
    (.block [.logic .or .a3 .a3 .a4, .li .t2 0, .sltu .t3 .t2 .s11, .sub .t3 .t2 .t3,
      .logic .xor .a3 .a3 .s6, .logic .and .a3 .a3 .t3, .logic .xor .s6 .s6 .a3]))

/-- One window, its digit at the top of `s7`: four squarings, `y := y T_d`,
the flag, then `s7 := s7 << 4`. -/
def window : Prog isa :=
  .seq square (.seq square (.seq square (.seq square
    (.seq (.block [.shift .srl .d .s11 .s7 60]) (.seq select (.seq (montOp aY aY aW)
      (.seq update (.block [.shift .sll .d .s7 .s7 4]))))))))

/-! ## The exponent -/

/-- The windows of `E`, its words from the top, 16 windows each. -/
def windows : Prog isa :=
  .seq (.block ([.li .s6 0, .addi .s9 .t0 0] ++ base .s8 aE ++ [.shift .sll .d .t2 .t0 3, .add .s8 .s8 .t2]))
    (.loop (.seq (.block [.addi .s8 .s8 (-8), .load .d .s7 .s8 0, .li .s10 16])
        (.seq (.loop (.seq window (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10))
          (.block [.addi .s9 .s9 (-1)])))
      (.nonzero .s9))

/-- `d :=` the 64-bit constant whose four 16-bit quarters are all `h`
(`h < 2^16`), through `tmp`: `lui`/`addi` build `h`, then two shifts and
`or`s repeat it. -/
def repeat16 (d tmp : Reg) (h : Nat) : List Instr :=
  let hi := (h + 0x800) / 0x1000
  [.lui d (BitVec.ofNat 20 hi), .addi d d ((h : Int) - (hi * 0x1000 : Nat)),
    .shift .sll .d tmp d 16, .logic .or d d tmp, .shift .sll .d tmp d 32, .logic .or d d tmp]

/-- The mask of `σ > j`: `l & K ≠ 0` for `l` the word after `E`, `K`'s
nibbles `0xD`, `0x9` or `0x1` for `j = 1, 2, 3`. -/
def sigK (j : Nat) : Nat := if j = 1 then 0xDDDD else if j = 2 then 0x9999 else 0x1111

/-- `t3 :=` the word `l` after `E`'s `w` words. -/
def loadL : List Instr := base .t3 aE ++ [.shift .sll .d .t2 .t0 3, .add .t3 .t3 .t2, .load .d .t3 .t3 0]

/-- A squaring after the windows: `y := y²`, the flag or'ed with `y = −1`
under the mask of `σ > j`. -/
def last (j : Nat) : Prog isa :=
  .seq (sqrOp aY aY aW) (.seq (eqMask .a3 aY aMinus)
    (.block (loadL ++ repeat16 .t4 .t5 (sigK j) ++ [.logic .and .t3 .t3 .t4, .li .t2 0, .sltu .t3 .t2 .t3,
      .sub .t3 .t2 .t3, .logic .and .a3 .a3 .t3, .logic .or .s6 .s6 .a3])))

/-- The round: the table, the windows, the three squarings. -/
def core : Prog isa :=
  .seq table (.seq windows (.seq (last 1) (.seq (last 2) (last 3))))

/-- `vg_miller_rabin_round`: the flag's low bit returned. -/
def round : Prog isa :=
  Impl.StackScratch.RISCV64.withStackScratch frameBytes .t2
    (.seq (.block (save ++ setup)) (.seq core (.block ([.li .a0 1, .logic .and .a0 .a0 .s6] ++ restore))))

end VG.Impl.MillerRabin.RISCV64
