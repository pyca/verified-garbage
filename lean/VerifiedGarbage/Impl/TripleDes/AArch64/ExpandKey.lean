module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Spec.TripleDes

/-! # Triple DES key expansion on AArch64

Every bit of a round key is one bit of its component key, the same one for
every key: PC-1, the rotations and PC-2 only move bits (FIPS 46-3, Appendix
1). So a component's sixteen round keys are selected from its 64 key bits
with `tbl`, whose time does not depend on its data: the table is 64 bytes
in `v16`–`v19`, byte `8 s + i` holding bit `s` of key byte `i` in its bit 0
(the component as a 64-bit word and that word shifted right by `s`), and
the indices are the static `tabWords`, at a public address. Two round keys
are 16 bytes of the schedule: for each of their bits `k`, one `tbl` gives
the 16 bytes' bit `k` in bit 0 of its bytes, and `sli` puts them together.
No key bit is an address or a branch condition.
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64.Key

open VG.AArch64

def tabName : String := "VG_TRIPLE_DES_KEY_SELECT"

/-- The rotation of the halves before round key `r` (from 0), from the key's. -/
def shiftOf (r : Nat) : Nat := ((List.range (r + 1)).map fun j => Spec.TripleDes.rotations.getD j 0).sum

/-- The key bit (FIPS's number, from 1, the most significant first) that is
bit `i` (from 0, the most significant first) of round key `r`. -/
def sel (r i : Nat) : Nat :=
  let q := Spec.TripleDes.pc2.getD i 1
  let u := if q ≤ 28 then (q - 1 + shiftOf r) % 28 + 1 else (q - 29 + shiftOf r) % 28 + 29
  Spec.TripleDes.pc1.getD (u - 1) 1

/-- The table's byte whose bit 0 is key bit `p`. -/
def keyIndex (p : Nat) : Nat := 8 * (7 - (p - 1) % 8) + (p - 1) / 8

/-- The index of byte `b` of round keys `2 pair` and `2 pair + 1` (eight
bytes each, the last two zero) for their bit `k`. -/
def idxByte (pair k b : Nat) : BitVec 8 :=
  if b % 8 < 6 then BitVec.ofNat 8 (keyIndex (sel (2 * pair + b / 8) (47 - (8 * (b % 8) + k))))
  else 0xFF

/-- Vector `8 pair + k` of the static: the sixteen indices for bit `k`. -/
def tabVec (j : Nat) : BitVec 128 := ofVBytes fun b => idxByte (j / 8) (j % 8) b

def tabWords : List (BitVec 64) :=
  (List.range 128).map fun i => (tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64

def tmp (k : Nat) : VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7].getD k .v0

/-- The table of the component key at `x0 + offset`. -/
def spread (offset : Nat) : List Instr :=
  [.ldr .x .x4 .x0 offset, .lsr .x .x5 .x4 1, .vop (.ins .d2 .v16 0 .x4), .vop (.ins .d2 .v16 1 .x5),
   .vop (.shift .ushr .d2 .v17 .v16 2), .vop (.shift .ushr .d2 .v18 .v16 4),
   .vop (.shift .ushr .d2 .v19 .v16 6)]

/-- Round keys `2 pair` and `2 pair + 1` to `x2 + out`. -/
def pairCode (pair out : Nat) : List Instr :=
  ((List.range 8).map fun k => .ldrqTbl (tmp k) .x6 (16 * (8 * pair + k)) tabName tabWords) ++
  ((List.range 8).map fun k => .vop (.tblN false 4 (tmp k) .v16 (tmp k))) ++
  ((List.range 7).map fun k => .vop (.shift .sli .b16 .v0 (tmp (k + 1)) (k + 1))) ++
  [.strq .v0 .x2 out]

def component (offset index : Nat) : Prog isa :=
  .block (spread offset ++ (List.range 8).flatMap fun pair => pairCode pair (128 * index + 16 * pair))

def copyThird : List Instr :=
  (List.range 16).flatMap fun j => [.ldr .x .x4 .x2 (8 * j), .str .x .x4 .x2 (256 + 8 * j)]

def expandKey : Prog isa :=
  .seq (.block [.adrSym .x6 tabName])
    (.seq (component 0 0)
      (.seq (component 8 1)
        (.seq (.block [.subImm .x .x4 .x1 16])
          (.ite (.zero .x .x4) (.block copyThird) (component 16 2)))))

end VG.Impl.TripleDes.AArch64.Key
