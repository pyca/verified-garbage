module

public import VerifiedGarbage.Impl.Tbl.AArch64
public import VerifiedGarbage.Spec.Seed

/-!
# SEED on one block by table lookups, on AArch64

`crypt d bufOff keyOff`: the block at `x5 + bufOff` enciphered or deciphered
in place under the schedule at `x5 + keyOff`, for the modes whose blocks
each need the one before, and for calls of a few blocks (the batch of
`Ecb.lean` does sixteen blocks in the time of about seven of these).
Decryption is encryption with the round keys from the last (`keyIdx`).

`S0` is in the table registers `v16`–`v31`, loaded by immediates
(`Impl.Tbl.AArch64.loadTable`), and the four bytes of `G`'s argument select
from it with `tbl` (`Impl.Tbl.AArch64.select`), whose time does not depend
on its data: no secret is an address or a branch condition. `S1` is an
affine function of `S0` (both are affine functions of a power of their
argument, `x²⁴⁷` and `x²⁵¹`, and `x²⁵¹ = (x²⁴⁷)¹²⁸`, which is linear over
GF(2)): `S1[x] = lo[S0[x] mod 16] ⊕ hi[S0[x] / 16]`, two lookups in tables
of sixteen bytes (`v4`, `v5`), kept for the bytes `X1` and `X3` (`bit`, by
the mask in `x16`).

`g`: `x10 := G(x10)`. With `Y = S1[X3] ‖ S0[X2] ‖ S1[X1] ‖ S0[X0]` back in
`x10`, RFC 4269 §2.2's `Z` is `(Y ∧ M0) ⊕ ((Y ∧ M1) ⋙ 8) ⊕ ((Y ∧ M2) ⋙ 16) ⊕
((Y ∧ M3) ⋙ 24)` (rotations), where byte `i` of `M_d` is `m_{(2i − d) mod 4}`:
`M0` is in `x17`, `M1` in `x4`, and `M2` and `M3` are those rotated by 8.

The block's words are in `x0`–`x3`, big-endian; a round XORs `F` of one
half into the other, and the halves change roles from round to round, so
that nothing is moved. Only `x0`–`x4`, `x6`–`x17`, `v0`–`v7` and `v16`–`v31`
are written, and no memory but the block.
-/

@[expose] public section

namespace VG.Impl.Seed.AArch64.Serial

open VG VG.AArch64 VG.Impl.Tbl.AArch64

/-- `S1[x] = loTable[S0[x] mod 16] ⊕ hiTable[S0[x] / 16]`. -/
def loTable : List (BitVec 8) :=
  [0x08, 0x98, 0x81, 0x11, 0x13, 0x83, 0x9a, 0x0a, 0xf8, 0x68, 0x71, 0xe1, 0xe3, 0x73, 0x6a, 0xfa]
def hiTable : List (BitVec 8) :=
  [0x00, 0xad, 0x3b, 0x96, 0x71, 0xdc, 0x4a, 0xe7, 0x6b, 0xc6, 0x50, 0xfd, 0x1a, 0xb7, 0x21, 0x8c]

/-- The bytes `X1` and `X3` of every word. -/
def oddMask : BitVec 32 := 0xff00ff00
/-- Byte `i` is `m_{2i mod 4}`. -/
def mask0 : BitVec 32 := 0xCFFCCFFC
/-- Byte `i` is `m_{(2i − 1) mod 4}`. -/
def mask1 : BitVec 32 := 0xF33FF33F

/-- `S0` into `v16`–`v31`, the tables of `S1` over `S0` into `v4` and `v5`,
64 and 128 into every byte of `v6` and `v7`, and 192, 15 and the masks into
`x14`–`x17` and `x4`. -/
def setup : List Instr :=
  loadTable (fun k => Spec.Seed.s0.getD k 0) ++
  const128 .v4 (ofVBytes fun e => loTable.getD e 0) ++ const128 .v5 (ofVBytes fun e => hiTable.getD e 0) ++
  [.movz .w .x15 64 0, .vop (.dup .b16 .v6 .x15), .movz .w .x15 128 0, .vop (.dup .b16 .v7 .x15),
   .movz .w .x14 192 0, .movz .w .x15 15 0] ++
  const64 .x16 (oddMask.setWidth 64) ++ const64 .x17 (mask0.setWidth 64) ++ const64 .x4 (mask1.setWidth 64)

/-- The word in `x10` in every lane of `v0`, and XORed with 64, 128 and 192
in `v1`–`v3`. -/
def indices : List Instr :=
  [.vop (.dup .s4 .v0 .x10), .vop (.logic .eor .v1 .v0 .v6), .vop (.logic .eor .v2 .v0 .v7),
   .vop (.dup .b16 .v3 .x14), .vop (.logic .eor .v3 .v0 .v3)]

/-- `S1` over `S0`, for the bytes `X1` and `X3` of `v0`. -/
def affine : List Instr :=
  [.vop (.dup .b16 .v1 .x15), .vop (.logic .and .v1 .v0 .v1), .vop (.shift .ushr .b16 .v2 .v0 4),
   .vop (.tbl .v1 .v4 .v1), .vop (.tbl .v2 .v5 .v2), .vop (.logic .eor .v1 .v1 .v2),
   .vop (.dup .s4 .v2 .x16), .vop (.bsel .bit .v0 .v1 .v2)]

/-- `Z` from `Y` in `x10`. -/
def mix : List Instr :=
  [.logic .and .w .x11 .x10 .x17, .logic .and .w .x12 .x10 .x4, .logicRor .eor .w .x11 .x11 .x12 8,
   .logicRor .and .w .x12 .x10 .x17 8, .logicRor .and .w .x13 .x10 .x4 8,
   .logicRor .eor .w .x12 .x12 .x13 8, .logicRor .eor .w .x10 .x11 .x12 16]

/-- `x10 := G(x10)`. -/
def g : List Instr := indices ++ select true ++ affine ++ [.umov .w .x10 .v0 0] ++ mix

/-- `(l0, l1) := (l0, l1) ⊕ F(K, (r0, r1))`, with the round key at
`x5 + koff`. -/
def f (l0 l1 r0 r1 : Reg) (koff : Nat) : List Instr :=
  [.ldr .w .x8 .x5 koff, .logic .eor .w .x8 .x8 r0, .ldr .w .x10 .x5 (koff + 4),
   .logic .eor .w .x10 .x10 r1, .logic .eor .w .x10 .x10 .x8] ++ g ++
  [.addImm .x .x9 .x10 0, .add .w .x10 .x10 .x8] ++ g ++
  [.addImm .x .x8 .x10 0, .add .w .x10 .x10 .x9] ++ g ++
  [.logic .eor .w l1 l1 .x10, .add .w .x10 .x10 .x8, .logic .eor .w l0 l0 .x10]

/-- The round key of round `i + 1` (from 0): encryption's from the first,
decryption's from the last (RFC 4269 §2.4). -/
def keyIdx : Spec.Seed.Direction → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 15 - i

/-- Rounds `2 j + 1` and `2 j + 2`: the first on `x0` and `x1`, the second
on `x2` and `x3`. -/
def round2 (d : Spec.Seed.Direction) (keyOff j : Nat) : List Instr :=
  f .x0 .x1 .x2 .x3 (keyOff + 8 * keyIdx d (2 * j)) ++ f .x2 .x3 .x0 .x1 (keyOff + 8 * keyIdx d (2 * j + 1))

/-- The register of word `i`. -/
def wordReg (i : Nat) : Reg := (#[.x0, .x1, .x2, .x3] : Array Reg)[i]!

/-- The block's words, big-endian, into `x0`–`x3`. -/
def loadBlock (bufOff : Nat) : List Instr :=
  (List.range 4).flatMap fun i => [.ldr .w (wordReg i) .x5 (bufOff + 4 * i), .rev32 (wordReg i) (wordReg i)]

/-- `R0, R1, L0, L1` back to the block. -/
def storeBlock (bufOff : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.rev32 (wordReg ((i + 2) % 4)) (wordReg ((i + 2) % 4)), .str .w (wordReg ((i + 2) % 4)) .x5 (bufOff + 4 * i)]

/-- The block at `x5 + bufOff` enciphered or deciphered in place, with the
schedule at `x5 + keyOff`. -/
def crypt (d : Spec.Seed.Direction) (bufOff keyOff : Nat) : List Instr :=
  setup ++ loadBlock bufOff ++ (List.range 8).flatMap (round2 d keyOff) ++ storeBlock bufOff

end VG.Impl.Seed.AArch64.Serial
