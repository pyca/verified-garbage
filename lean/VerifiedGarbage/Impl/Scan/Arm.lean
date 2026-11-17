module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# Constant-time table lookups on ARMv7: choosing a row of eight words

A lookup in a table never uses the secret index as an address: it reads the
whole table. The table is 32 *rows* of eight words (its *columns*), whose
addresses are public. The index's high five bits, the number of its row,
are a one-hot word (`oneHot`: bit `h` of `r2` for row `h`, five conditional
shifts, each a multiplication by 1 or by a power of two), and each row has a
mask from its bit, all ones for the index's row and zero for the others
(`rowMask`). Each word of the row is loaded and kept under that mask in its
column's register, `r4`–`r11` (`word`): in half of the columns by `and` and
`orr`, in the other half by `mla`, a multiplication by the mask added to
the column, which leaves the word's negation (`mlaCol`: a core has one
multiplier, and the two kinds share the work between it and the others).
After the 32 rows the columns hold the eight words of the index's row
(`rows`), and the caller chooses among them by the index's low three bits.

The rows are four groups of eight: a loop of four iterations, whose count is
in the slot at `cnt` of the working space at `r12`, the one-hot word shifted
right by eight bits and the table's pointer `lr` moved on by `stride` after
each. `r0` is a temporary, `r1` the row's mask, `r3` holds 1.
-/

@[expose] public section

namespace VG.Impl.Scan.Arm

open VG.Arm

/-- The register of column `c` (0–7). -/
def colReg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | _ => .r11

/-- Whether column `c` accumulates by `mla`, and so holds the negation of
its word: columns 2, 3, 6 and 7. -/
def mlaCol (c : Nat) : Bool := c / 2 % 2 == 1

/-- A step of the one-hot word: `r2` shifted left by `2 ^ b` if bit `3 + b`
of the index in `r0` is set (a multiplication by `1 + bit * (2 ^ 2 ^ b - 1)`). -/
def ohStep (b : Nat) : List Instr :=
  [.dp .and .r1 .r3 (.shifted .r0 .lsr (3 + b)), .dp .add .lr .r3 (.shifted .r1 .lsl (2 ^ b)),
   .dp .sub .lr .lr (.reg .r1), .mul .r2 .r2 .lr]

/-- `r3` := 1 and `r2` := the one-hot word of the row of the index in `r0`
(below 256): bit `r0 >> 3`. Clobbers `r1` and `lr`. -/
def oneHot : List Instr :=
  ([.mov .r3 (.imm 1), .dp .and .r1 .r3 (.shifted .r0 .lsr 3), .dp .add .r2 .r3 (.reg .r1)] : List Instr) ++
    ohStep 1 ++ ohStep 2 ++ ohStep 3 ++ ohStep 4

/-- The columns := 0. -/
def clear : List Instr :=
  [.mov .r4 (.imm 0), .mov .r5 (.imm 0), .mov .r6 (.imm 0), .mov .r7 (.imm 0), .mov .r8 (.imm 0),
   .mov .r9 (.imm 0), .mov .r10 (.imm 0), .mov .r11 (.imm 0)]

/-- The one-hot word of the index in `r0`, and the columns cleared. -/
def start : List Instr := oneHot ++ clear

/-- The word at `off` from `lr` into column `c`, under the row's mask in `r1`. -/
def word (off c : Nat) : List Instr :=
  if mlaCol c then [.ldr .r0 .lr off, .mla (colReg c) .r0 .r1 (colReg c)]
  else [.ldr .r0 .lr off, .dp .and .r0 .r0 (.reg .r1), .dp .orr (colReg c) (colReg c) (.reg .r0)]

/-- `r1` := the mask of row `r` of the group: all ones if bit `r` of the
one-hot word in `r2` is set, else zero. -/
def rowMask (r : Nat) : List Instr :=
  [.dp .bic .r1 .r3 (if r = 0 then .reg .r2 else .shifted .r2 .lsr r), .dp .sub .r1 .r1 (.imm 1)]

/-- Row `r` of the group, its word of column `c` at `offs r c` from `lr`. -/
def row (offs : Nat → Nat → Nat) (r : Nat) : List Instr :=
  rowMask r ++ (List.range 8).flatMap fun c => word (offs r c) c

/-- On to the next group (Z set after the last). -/
def groupEnd (stride cnt : Nat) : List Instr :=
  [.mov .r2 (.shifted .r2 .lsr 8), .dp .add .lr .lr (.imm (BitVec.ofNat 32 stride)), .ldr .r0 .r12 cnt,
   .subs .r0 .r0 (.imm 1), .str .r0 .r12 cnt]

/-- A group of eight rows. -/
def group (offs : Nat → Nat → Nat) (stride cnt : Nat) : List Instr :=
  (List.range 8).flatMap (row offs) ++ groupEnd stride cnt

/-- The 32 rows of the table at `lr`, a group `stride` bytes after the one
before it, after `start`: column `c` := the word of column `c` of the row
whose bit is set in `r2` (negated if `mlaCol c`). Clobbers `r0`, `r1`, `r2`
and `lr`, and the slot at `cnt` of the working space at `r12`. -/
def rows (offs : Nat → Nat → Nat) (stride cnt : Nat) : Prog isa :=
  .seq (.block [.mov .r0 (.imm 4), .str .r0 .r12 cnt]) (.loop (.block (group offs stride cnt)) .ne)

end VG.Impl.Scan.Arm
