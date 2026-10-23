module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # RC2 table lookups on PPC64LE

A secret-indexed lookup scans every doubleword of its table in a fixed
order, from the last to the first, at addresses that depend only on the
row: the schedule's 16 doublewords (four 16-bit entries each) or PITABLE's
32 (eight bytes each, in the working space). The index is held as the
entry's byte offset `q` in `r10`. Row `k` holds the entry exactly when
`(q XOR 8k) >> 3` is zero, so `(((q XOR 8k) >> 3) - 1) >> 63` is 1 exactly
then, and less one, a mask that is all ones exactly when the row does *not*
hold it: the row's doubleword is ANDed with the mask and XORed with itself,
leaving it or zero, and ORed into the accumulator `r11`. The entry's lane is
then rotated to the bottom by rotations selected by masks of `q`'s low bits,
as Blowfish's lookups do (`Impl/Blowfish/PPC64LE.lean`). The index is only
ever an operand of the masks' arithmetic; there are no comparisons.

Registers: the table at `base`, the row pointer in `rp`, `q` in `r10`, the
accumulator (and result) in `r11`, the mask in `r12`, a temporary in `r0`.
-/

@[expose] public section

namespace VG.Impl.Rc2.PPC64LE

open VG.PPC64LE

/-- Keep the low `n` bits of `r`. -/
def mask (r : Reg) (n : Nat) : List Instr := [.lsl r r (64 - n), .lsr .d r r (64 - n)]

/-- The accumulator and the row pointer at the last of `rows` rows. -/
def scanStart (base rp : Reg) (rows : Nat) : List Instr := [.li .r11 0, .addi rp base (8 * (rows - 1))]

/-- One row: the doubleword at `rp`, kept if it holds the entry, into the
accumulator; the previous row, and `r0` zero after the first row. -/
def scanRow (base rp : Reg) : List Instr :=
  [.sub .r0 rp base, .logic .xor .r12 .r10 .r0, .lsr .d .r12 .r12 3, .subi .r12 .r12 1,
   .lsr .d .r12 .r12 63, .subi .r12 .r12 1, .load .d .r0 rp 0, .logic .and .r12 .r0 .r12,
   .logic .xor .r0 .r0 .r12, .logic .or .r11 .r11 .r0, .sub .r0 rp base, .subi rp rp 8]

/-- The accumulator rotated right by `8 * 2 ^ c` if bit `c` of `q` is set:
`x := rot XOR ((rot XOR x) AND m)` for the mask `m` that is all ones
exactly when the bit is clear. -/
def condRot (c : Nat) : List Instr :=
  [.lsl .r12 .r10 (63 - c), .lsr .d .r12 .r12 63, .subi .r12 .r12 1, .rotr .d .r0 .r11 (8 * 2 ^ c),
   .logic .xor .r11 .r11 .r0, .logic .and .r11 .r11 .r12, .logic .xor .r11 .r11 .r0]

/-- The entry at byte offset `q` of the table of `rows` doublewords at
`base`, of `bits` bits, its lane selected by the bits `lanes` of `q`, into
`r11`. -/
def scan (base rp : Reg) (rows : Nat) (lanes : List Nat) (bits : Nat) : Prog isa :=
  .seq (.block (scanStart base rp rows))
    (.seq (.loop (.block (scanRow base rp)) (.nonzero .d .r0))
      (.block (lanes.flatMap condRot ++ mask .r11 bits)))

/-- `r11 := schedule[q / 2]`, the 16-bit entry at byte offset `q` of the
schedule at `r3`, through the row pointer `r5`. -/
def keyLookup : Prog isa := scan .r3 .r5 16 [1, 2] 16

end VG.Impl.Rc2.PPC64LE
