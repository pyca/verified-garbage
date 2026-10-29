module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-! # RC2 table lookups on RISC-V

The lookups of the PPC64LE implementation (`Impl/Rc2/PPC64LE/Lookup.lean`):
a secret-indexed lookup scans every doubleword of its table in a fixed
order, from the last to the first, at addresses that depend only on the
row: the 16 doublewords of the schedule's copy (four 16-bit entries each) or
PITABLE's 32 (eight bytes each), both in the working space, which the
contracts align to 8 bytes. The index is held as the entry's byte offset `q`
in `t0`. Row `k` holds the entry exactly when `(q XOR 8k) >> 3` is zero, so
`(((q XOR 8k) >> 3) - 1) >> 63` is 1 exactly then, and less one, a mask
that is all ones exactly when the row does *not* hold it: the row's
doubleword is ANDed with the mask and XORed with itself, leaving it or zero,
and ORed into the accumulator `t1`. The entry is then shifted to the bottom
by shifts selected by masks of `q`'s low bits (there are no rotate
instructions; the bits a shift drops are above the entry). The index is only
ever an operand of the masks' arithmetic; there are no comparisons.

Registers: the table at `base`, the row pointer in `rp`, `q` in `t0`, the
accumulator (and result) in `t1`, the mask in `t2`, a temporary in `a7`.
-/

@[expose] public section

namespace VG.Impl.Rc2.RISCV64

open VG.RISCV64

/-- Keep the low `n` bits of `r`. -/
def mask (r : Reg) (n : Nat) : List Instr := [.shift .sll .d r r (64 - n), .shift .srl .d r r (64 - n)]

/-- The accumulator and the row pointer at the last of `rows` rows. -/
def scanStart (base rp : Reg) (rows : Nat) : List Instr :=
  [.li .t1 0, .addi rp base (8 * (rows - 1) : Nat)]

/-- One row: the doubleword at `rp`, kept if it holds the entry, into the
accumulator; the previous row, and `a7` zero after the first row. -/
def scanRow (base rp : Reg) : List Instr :=
  [.sub .a7 rp base, .logic .xor .t2 .t0 .a7, .shift .srl .d .t2 .t2 3, .addi .t2 .t2 (-1),
   .shift .srl .d .t2 .t2 63, .addi .t2 .t2 (-1), .load .d .a7 rp 0, .logic .and .t2 .a7 .t2,
   .logic .xor .a7 .a7 .t2, .logic .or .t1 .t1 .a7, .sub .a7 rp base, .addi rp rp (-8)]

/-- The accumulator shifted right by `8 * 2 ^ c` if bit `c` of `q` is set:
`x := sh XOR ((sh XOR x) AND m)` for the mask `m` that is all ones exactly
when the bit is clear. -/
def condShift (c : Nat) : List Instr :=
  [.shift .sll .d .t2 .t0 (63 - c), .shift .srl .d .t2 .t2 63, .addi .t2 .t2 (-1),
   .shift .srl .d .a7 .t1 (8 * 2 ^ c), .logic .xor .t1 .t1 .a7, .logic .and .t1 .t1 .t2,
   .logic .xor .t1 .t1 .a7]

/-- The entry at byte offset `q` of the table of `rows` doublewords at
`base`, of `bits` bits, its lane selected by the bits `lanes` of `q`, into
`t1`. -/
def scan (base rp : Reg) (rows : Nat) (lanes : List Nat) (bits : Nat) : Prog isa :=
  .seq (.block (scanStart base rp rows))
    (.seq (.loop (.block (scanRow base rp)) (.nonzero .a7))
      (.block (lanes.flatMap condShift ++ mask .t1 bits)))

/-- `t1 := schedule[q / 2]`, the 16-bit entry at byte offset `q` of the
schedule's copy at `a2`, through the row pointer `t3`. -/
def keyLookup : Prog isa := scan .a2 .t3 16 [1, 2] 16

end VG.Impl.Rc2.RISCV64
