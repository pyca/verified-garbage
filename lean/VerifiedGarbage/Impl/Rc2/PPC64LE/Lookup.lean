module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # RC2 table lookups on PPC64LE

A secret-indexed lookup reads every 32 bytes of its table (two vectors,
`lxvd2x`) at addresses that depend only on the chunk: the schedule's 128
bytes (64 16-bit entries) or PITABLE's 256 (in the working space). The index
is held as the entry's byte offset `q` in `r10`. In each chunk `vperm` picks
the entry's byte or two bytes at offset `q mod 32` (the control byte `q XOR
7`, as `lxvd2x` numbers the bytes it loads `XOR 7`), into bytes 0 and 1 of a
vector, and a tree of `vsel` by masks of `q`'s bits 5, 6 and 7 picks the
chunk `q >> 5`. The index is only ever an operand of the masks' arithmetic
and of `vperm`, whose time does not depend on its operands; there are no
comparisons.

Registers: the table at `base`, the chunk pointer in `rp`, `q` in `r10`, the
result in `r11`, temporaries `r0` and `r12`, and `v0`–`v13`.
-/

@[expose] public section

namespace VG.Impl.Rc2.PPC64LE

open VG.PPC64LE

/-- Keep the low `n` bits of `r`. -/
def mask (r : Reg) (n : Nat) : List Instr := [.lsl r r (64 - n), .lsr .d r r (64 - n)]

/-- The vector registers: the control, the masks of bits 5, 6 and 7, the two
halves of a chunk, and each chunk's pick. -/
def vCtl : VReg := .v0
def vBit : Nat → VReg
  | 5 => .v1 | 6 => .v2 | _ => .v3
def vLo : VReg := .v4
def vHi : VReg := .v5
def vPick : Nat → VReg
  | 0 => .v6 | 1 => .v7 | 2 => .v8 | 3 => .v9 | 4 => .v10 | 5 => .v11 | 6 => .v12 | _ => .v13

/-- The control: `q XOR 7` in byte 0, and `(q + 1) XOR 7` in byte 1 for a
16-bit entry. -/
def ctl (two : Bool) : List Instr :=
  [.li .r0 7, .logic .xor .r12 .r10 .r0, .lsl .r12 .r12 56] ++
  (if two then [.addi .r11 .r10 1, .logic .xor .r11 .r11 .r0, .lsl .r11 .r11 56, .lsr .d .r11 .r11 8,
    .logic .or .r12 .r12 .r11] else []) ++ [.mtvsrd vCtl .r12]

/-- The mask of bit `b` of `q`: all ones if it is set, else zero, in the
first doubleword. -/
def bitMask (b : Nat) : List Instr :=
  [.lsl .r12 .r10 (63 - b), .lsr .d .r12 .r12 63, .li .r0 0, .sub .r12 .r0 .r12, .mtvsrd (vBit b) .r12]

/-- Chunk `i`'s pick, and the chunk pointer to the next chunk. -/
def chunk (rp : Reg) (i : Nat) : List Instr :=
  [.lxvd2x vLo rp .r0, .lxvd2x vHi rp .r12, .vop (.perm (vPick i) vLo vHi vCtl), .addi rp rp 32]

/-- `vPick d` := `vPick d` or `vPick n`, as bit `b` of `q` says. -/
def choose (b d n : Nat) : Instr := .vop (.sel (vPick d) (vPick d) (vPick n) (vBit b))

/-- The entry at byte offset `q` (in `r10`) of the table of four chunks
(the schedule) or eight (`eight`, PITABLE), of one byte or two (`two`),
into `r11`. -/
def vscan (base rp : Reg) (eight two : Bool) : List Instr :=
  ctl two ++ bitMask 5 ++ bitMask 6 ++ (if eight then bitMask 7 else []) ++
  [.li .r0 0, .li .r12 16, .logic .or rp base base] ++
  chunk rp 0 ++ chunk rp 1 ++ chunk rp 2 ++ chunk rp 3 ++
  (if eight then chunk rp 4 ++ chunk rp 5 ++ chunk rp 6 ++ chunk rp 7 else []) ++
  [choose 5 0 1, choose 5 2 3, choose 6 0 2] ++
  (if eight then [choose 5 4 5, choose 5 6 7, choose 6 4 6, choose 7 0 4] else []) ++
  [.mfvsrd .r11 (vPick 0)] ++
  (if two then [.lsl .r12 .r11 8, .lsr .d .r12 .r12 56, .lsr .d .r11 .r11 56, .lsl .r12 .r12 8,
    .logic .or .r11 .r11 .r12] else [.lsr .d .r11 .r11 56])

/-- `r11 := schedule[q / 2]`, the 16-bit entry at byte offset `q` of the
schedule at `r3`, through the chunk pointer `r5`. -/
def keyLookup : Prog isa := .block (vscan .r3 .r5 false true)

end VG.Impl.Rc2.PPC64LE
