module

public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Impl.Tbl.AArch64

/-! # RC2 table lookups on AArch64

Both lookups select from a table in the table registers with `tbl`
(`Impl/Tbl/AArch64.lean`), so that no secret is ever an address or a branch
condition: PITABLE is built from immediates in `v16`–`v31` at each lookup,
and a schedule word is read from the 128-byte schedule at `x0` into
`v16`–`v23`. Only caller-saved vector registers are written (`v0`–`v5`,
`v16`–`v31`).
-/

@[expose] public section

namespace VG.Impl.Rc2.AArch64

open VG.AArch64 VG.Impl.Tbl.AArch64

def rr (dst src : Reg) : Instr := .addImm .x dst src 0
def imm (dst : Reg) (n : Nat) : Instr := .movz .x dst (BitVec.ofNat 16 n) 0

/-- Keep the low `n` bits without needing a logical-immediate instruction. -/
def mask (r : Reg) (n : Nat) : List Instr :=
  [.lsl .x r r (64 - n), .lsr .x r r (64 - n)]

/-- The index in `v0`, XORed with 64 into `v1`; with 128 and 192 into `v2`
and `v3` if `full` (a table of 256 bytes rather than 128), through `x6` and
`v4`, `v5`. -/
def quarters (full : Bool) : List Instr :=
  [imm .x6 64, .vop (.dup .b16 .v4 .x6), .vop (.logic .eor .v1 .v0 .v4)] ++
  if full then
    [imm .x6 128, .vop (.dup .b16 .v5 .x6), .vop (.logic .eor .v2 .v0 .v5),
     .vop (.logic .eor .v3 .v1 .v5)]
  else []

/-- PITABLE of the low byte of `x8`, returned in `x8`. -/
def piLookup : List Instr :=
  loadTable (fun k => Spec.Rc2.piTable.getD k 0) ++ ([.vop (.dup .b16 .v0 .x8)] : List Instr) ++ quarters true ++
    select true ++
    ([.umov .w .x8 .v0 0] : List Instr) ++ mask .x8 8

/-- Load schedule word `i` at `x0` into `x4`, using byte accesses. -/
def loadKey (i : Nat) : List Instr :=
  [.ldrb .x4 .x0 (2 * i), .ldrb .x5 .x0 (2 * i + 1),
   .ror .x .x5 .x5 56, .logic .orr .x .x4 .x4 .x5]

/-- The schedule at `x0` into `v16`–`v23`. -/
def loadSchedule : List Instr := (List.range 8).map fun r => .ldrq (treg r) .x0 (16 * r)

/-- Select schedule word `j = x8 & 63`, returned in `x8`: its bytes `2 j` and
`2 j + 1` are the indices of the low two lanes of each word of `v0`
(`514 j + 256`, through `x3` and `x6`). -/
def keyLookup : List Instr :=
  mask .x8 6 ++ loadSchedule ++
  [imm .x3 514, imm .x6 256, .madd .x .x8 .x8 .x3 .x6, .vop (.dup .s4 .v0 .x8)] ++
  quarters false ++ select false ++ ([.umov .w .x8 .v0 0] : List Instr) ++ mask .x8 16

end VG.Impl.Rc2.AArch64
