module

public import VerifiedGarbage.Impl.P384.EcdhDouble
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb

/-!
# P-384's table entry for ECDH's window on AArch64, selected by vectors

An entry of the window's table is three coordinates of six words, so nine
vector registers hold one: `sel` keeps the entry selected so far in nine
accumulators, which start as `(0 : R : 0)`, the entry of a digit of magnitude
zero. It reads the eight entries in turn, at addresses that depend on no digit,
and inserts each under a mask which is all ones only for the entry whose number,
counted in both lanes of `v30`, is the digit's magnitude, then stores the
accumulators into `E`, whose coordinates are consecutive. It writes 22 of the
vector registers the calling convention does not preserve, all but `v18` and
`v29`.
-/

@[expose] public section

namespace VG.Impl.P384.EcdhSelect
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble

/-- The accumulators (three to a coordinate),
the registers an entry is loaded into, its number and its mask. -/
def bank : SelGroup :=
  ⟨[.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16],
   [.v17, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27], .v30, .v31⟩

/-- Accumulator `i`, and the register pair `i` of an entry is loaded into. -/
def acc (i : Nat) : VReg := bank.acc.getD i .v0
def ld (i : Nat) : VReg := bank.ld.getD i .v20

/-- The magnitude in both lanes of `v19`, `1` in both of `v28`, and no entry
counted yet. -/
def count : List Instr :=
  [.movz .x .x5 1 0, .vop (.dup .d2 .v19 .x2), .vop (.dup .d2 .v28 .x5), .vop (.movi0 bank.idx)]

/-- The accumulators `(0 : R : 0)`: for P-384, `R mod p = 2^128 + 2^96 - 2^32 + 1`,
whose words are `2^64 - (2^32 - 1)`, `2^32 - 1` and `1`, from `x5 = 1`. -/
def start : List Instr :=
  bank.acc.map (fun v => .vop (.movi0 v)) ++
  ([.lsl .x .x4 .x5 32, .sub .x .x6 .x4 .x5, .sub .x .x4 .x5 .x4,
    .vop (.ins .d2 .v3 0 .x4), .vop (.ins .d2 .v3 1 .x6), .vop (.ins .d2 .v4 0 .x5)] : List Instr)

/-- Entry `m + 1` inserted if it is the magnitude's. -/
def entry (m : Nat) : List Instr :=
  [.vop (.add .d2 bank.idx bank.idx .v28), .vop (.cmeq .d2 bank.mask bank.idx .v19)] ++
  (((List.range 9).map fun i => .ldrq (ld i) .x0 (K.tbl + 144 * m + 16 * i) : List Instr) ++
  ((List.range 9).map fun i => .vop (.bsel .bit (acc i) (ld i) bank.mask) : List Instr))

/-- The entry of digit `x19` into `E`. -/
def sel : List Instr :=
  nibble K.bits ++ (magnitude ++ (count ++ (start ++ ((List.range 8).flatMap entry ++
    ((List.range 9).map fun i => .strq (acc i) .x0 (K.E.x + 16 * i) : List Instr)))))

end VG.Impl.P384.EcdhSelect
