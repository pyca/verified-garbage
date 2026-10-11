module

public import VerifiedGarbage.TCB.AArch64.Isa

/-! # Table lookups with `tbl` on AArch64

A table of up to 256 bytes is held in `v16`–`v31` (`treg`), sixteen bytes
per register, and a secret index selects from it with `tbl`, which takes a
time independent of its data (see `TCB/AArch64/Isa.lean`): four registers
per `tbl`, one `tbl` per 64 bytes of the table (a *quarter*), on the index
XORed with the quarter's number (in `v0`–`v3`), which only that quarter's
`tbl` finds in range (any other gives 0), and the results ORed together. No
secret is ever an address or a branch condition.
-/

@[expose] public section

namespace VG.Impl.Tbl.AArch64

open VG.AArch64

/-- The table register `r`. -/
def treg (r : Nat) : VReg :=
  [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
   .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31].getD r .v16

/-- The first register of quarter `q` of the table (bytes `64 q … 64 q + 63`). -/
def quarter (q : Nat) : VReg := treg (4 * q)

/-- The table's bytes at the indices in `v0` (and `v1`, `v2`, `v3`, the
indices XORed with 64, 128 and 192), in `v0`; with only `v0` and `v1` for a
table of 128 bytes (`full` false). -/
def select (full : Bool) : List Instr :=
  [.vop (.tblN false 4 .v0 (quarter 0) .v0), .vop (.tblN false 4 .v1 (quarter 1) .v1)] ++
  (if full then
    [.vop (.tblN false 4 .v2 (quarter 2) .v2), .vop (.tblN false 4 .v3 (quarter 3) .v3),
     .vop (.logic .orr .v2 .v2 .v3)]
  else []) ++
  [.vop (.logic .orr .v0 .v0 .v1)] ++ (if full then [.vop (.logic .orr .v0 .v0 .v2)] else [])

/-- `r := v`, a 64-bit constant. -/
def const64 (r : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x r (v.extractLsb' 0 16) 0, .movk .x r (v.extractLsb' 16 16) 1,
   .movk .x r (v.extractLsb' 32 16) 2, .movk .x r (v.extractLsb' 48 16) 3]

/-- The 128-bit constant `v` into `d`, through `x6` and `x7`. -/
def const128 (d : VReg) (v : BitVec 128) : List Instr :=
  const64 .x6 (v.extractLsb' 0 64) ++ const64 .x7 (v.extractLsb' 64 64) ++
    [.vop (.ins .d2 d 0 .x6), .vop (.ins .d2 d 1 .x7)]

/-- The table `t` (byte `k` is `t k`) into the table registers, through `x6` and `x7`. -/
def loadTable (t : Nat → BitVec 8) : List Instr :=
  (List.range 16).flatMap fun r => const128 (treg r) (ofVBytes fun e => t (16 * r + e))

end VG.Impl.Tbl.AArch64
