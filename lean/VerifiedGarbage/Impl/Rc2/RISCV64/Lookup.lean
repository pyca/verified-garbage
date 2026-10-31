module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-! # RC2 table lookups on RISC-V

A secret-indexed lookup scans every doubleword of its table, with its rows
unrolled, at addresses that depend only on the row: the 16 doublewords of
the schedule's copy (four 16-bit entries each) or PITABLE's 32 (eight bytes
each), both in the working space, which the contracts align to 8 bytes.
The index is held as the entry's byte offset `q` in `t0`, and its row as
one bit, `2 ^ (q >> 3)` (1 shifted left by the row, `sll`), in `t3`: row
`k`'s mask is its bit `k` shifted to the top and arithmetically back, all
ones exactly when the row holds the entry, and the row's doubleword ANDed
with it is ORed into the accumulator `t1`. The entry is then shifted to the
bottom by eight times its offset in the doubleword (`srl` by a register)
and masked. The index is only ever an operand of the masks' and the
shifts' arithmetic; there are no comparisons.

Registers: the table at `base`, `q` in `t0`, the accumulator (and result)
in `t1`, the mask in `t2`, the row's bit in `t3`, a temporary in `a7`.
-/

@[expose] public section

namespace VG.Impl.Rc2.RISCV64

open VG.RISCV64

/-- Keep the low `n` bits of `r`. -/
def mask (r : Reg) (n : Nat) : List Instr := [.shift .sll .d r r (64 - n), .shift .srl .d r r (64 - n)]

/-- `t3 := 1 << (q >> 3)`, a bit at the index's row, through `t2`. -/
def rowBit : List Instr :=
  [.shift .srl .d .t3 .t0 3, .li .t2 1, .shiftReg .sll .d .t3 .t2 .t3]

/-- Row `k`'s mask into `t2`: all ones if bit `k` of `t3` is set, else zero. -/
def rowMask (k : Nat) : List Instr := [.shift .sll .d .t2 .t3 (63 - k), .shift .sra .d .t2 .t2 63]

/-- Row 0 of the table at `base`, masked, into the accumulator. -/
def row0 (base : Reg) : List Instr := rowMask 0 ++ [.load .d .t1 base 0, .logic .and .t1 .t1 .t2]

/-- Row `k`, masked, ORed into the accumulator. -/
def row (base : Reg) (k : Nat) : List Instr :=
  rowMask k ++ [.load .d .a7 base (8 * k), .logic .and .a7 .a7 .t2, .logic .or .t1 .t1 .a7]

/-- Rows `0, …, n` of the table at `base`. -/
def rowsCode (base : Reg) (n : Nat) : List Instr := row0 base ++ (List.range n).flatMap fun i => row base (i + 1)

/-- The accumulator shifted right by eight times the lane's offset, the bits
`q AND laneBits`. -/
def laneCode (laneBits : Nat) : List Instr :=
  [.logicImm .and .t2 .t0 laneBits, .shift .sll .d .t2 .t2 3, .shiftReg .srl .d .t1 .t1 .t2]

/-- The entry at byte offset `q` of the table of `rows` doublewords at
`base`, of `bits` bits, its lane the bits `q AND laneBits`, into `t1`: the
rows (only the index's survives its mask), then shifted right by eight
times the lane's offset, and masked. -/
def scan (base : Reg) (rows : Nat) (laneBits : Nat) (bits : Nat) : Prog isa :=
  .block (rowBit ++ rowsCode base (rows - 1) ++ laneCode laneBits ++ mask .t1 bits)

/-- `t1 := schedule[q / 2]`, the 16-bit entry at byte offset `q` of the
schedule's copy at `a2`. -/
def keyLookup : Prog isa := scan .a2 16 6 16

end VG.Impl.Rc2.RISCV64
