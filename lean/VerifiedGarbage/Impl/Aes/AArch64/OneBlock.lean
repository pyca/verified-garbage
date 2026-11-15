module

public import VerifiedGarbage.Impl.Tbl.AArch64

/-!
# AES encryption of one block by table lookups, on AArch64

`core`: `v0 := CIPHER(v0)` with the key schedule at `x0` and `x1` rounds, in
the baseline ISA, for the functions that are given one block at a time (the
bitsliced code, four blocks at a time, first bitslices every round key).

The S-box is in the table registers `v16`–`v31`, loaded by immediates
(`Impl.Tbl.AArch64.loadTable`), and a state byte selects from it with `tbl`,
whose time does not depend on its data (`Impl.Tbl.AArch64.select`): no
secret is an address or a branch condition. The state is in `v0`, as FIPS
197 lays it out (byte `r + 4c` is `s[r, c]`), already XORed with the round
key. A round is:

* ShiftRows: one `tbl` of the state by the indices in `v4` (`shiftIdx`);
* SubBytes: the state XORed with 64, 128 and 192 (from `v6` and `v5`) in
  `v1`–`v3`, and `select`;
* MixColumns (`mix`): with `2 • x` (`shl` by 1, XORed with `0x1b` where the
  byte's top bit, spread by `sshr`, was set) and the rotations of the
  columns, which are the 32-bit lanes, by two bytes (`rev32` of the 16-bit
  halves) and by one (`ushr` and `sli`): `y = 2 • x ⊕ rot₂ x`, and
  `rot₁ (x ⊕ y) ⊕ y`, whose byte `t` is `2 • x_t ⊕ 3 • x_{t+1} ⊕ x_{t+2} ⊕
  x_{t+3}`;
* AddRoundKey: `eor` with the next 16 bytes of the schedule.

The last round has no MixColumns. Only `x0`, `x1`, `x6`, `x7`, `v0`–`v7`
and `v16`–`v31` are written.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.OneBlock

open VG.AArch64 VG.Impl.Tbl.AArch64

/-- ShiftRows as the indices of a `tbl`: byte `t` of the result is byte
`t mod 4 + 4 ((t / 4 + t mod 4) mod 4)` of the state. -/
def shiftIdx : BitVec 128 := ofVBytes fun t => BitVec.ofNat 8 (t % 4 + 4 * ((t / 4 + t % 4) % 4))

/-- The S-box into `v16`–`v31`, ShiftRows' indices into `v4`, and the bytes
`0x80`, `0x40` and `0x1b` into every byte of `v5`, `v6` and `v7`. -/
def setup : List Instr :=
  loadTable (fun k => aesSbox (BitVec.ofNat 8 k)) ++ const128 .v4 shiftIdx ++
  [.movz .w .x6 0x80 0, .vop (.dup .b16 .v5 .x6), .movz .w .x6 0x40 0, .vop (.dup .b16 .v6 .x6),
    .movz .w .x6 0x1b 0, .vop (.dup .b16 .v7 .x6)]

/-- ShiftRows, then SubBytes, of `v0`. -/
def subShift : List Instr :=
  [.vop (.tbl .v0 .v0 .v4), .vop (.logic .eor .v1 .v0 .v6), .vop (.logic .eor .v2 .v0 .v5),
    .vop (.logic .eor .v3 .v1 .v5)] ++ select true

/-- MixColumns of `v0`. -/
def mix : List Instr :=
  [.vop (.shift .sshr .b16 .v1 .v0 7), .vop (.shift .shl .b16 .v2 .v0 1), .vop (.logic .and .v1 .v1 .v7),
    .vop (.logic .eor .v2 .v2 .v1), .vop (.rev .rev32h .v1 .v0), .vop (.logic .eor .v2 .v2 .v1),
    .vop (.logic .eor .v0 .v0 .v2), .vop (.shift .ushr .s4 .v1 .v0 8), .vop (.shift .sli .s4 .v1 .v0 24),
    .vop (.logic .eor .v0 .v1 .v2)]

/-- A full round, with the next round key: `x0` to it, and one round fewer
left in `x1`. -/
def round : List Instr :=
  subShift ++ mix ++
    [.addImm .x .x0 .x0 16, .ldrq .v1 .x0 0, .vop (.logic .eor .v0 .v0 .v1), .subImm .x .x1 .x1 1]

/-- The rounds: AddRoundKey, `x1 − 1` full rounds, and the last. -/
def rounds : Prog isa :=
  .seq (.block [.ldrq .v1 .x0 0, .vop (.logic .eor .v0 .v0 .v1), .subImm .x .x1 .x1 1])
    (.seq (.loop (.block round) (.nonzero .x .x1))
      (.block (subShift ++ [.ldrq .v1 .x0 16, .vop (.logic .eor .v0 .v0 .v1)])))

/-- `v0 := CIPHER(v0)`, with the key schedule at `x0` and `x1` rounds. -/
def core : Prog isa := .seq (.block setup) rounds

end VG.Impl.Aes.AArch64.OneBlock
