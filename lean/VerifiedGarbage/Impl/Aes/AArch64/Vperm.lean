module

public import VerifiedGarbage.Impl.Aes.Vperm
public import VerifiedGarbage.Impl.Tbl.AArch64

/-!
# AES encryption of one block by vector permutations, on AArch64

`core`: `v0 := CIPHER(v0)` with the key schedule at `x0` and `x1` rounds, in
the baseline ISA, for the functions that are given one block at a time (the
bitsliced code, eight blocks at a time, first bitslices every round key).

Every table is one register of sixteen bytes, which a four-bit index selects
from with a one-register `tbl`, whose time does not depend on its data: no
secret is an address or a branch condition. An index of 16 or more selects 0.

A byte `x` of the state is `i • A + k` for two elements `i` and `k` of the
subfield GF(2⁴) of GF(2⁸), where `A² + a • A + a = 0` for an `a` of the
subfield; the state is kept as the bytes `L x`, whose high and low four bits
are `i` and `k` in a basis of the subfield (`keyLo` and `keyHi` are `L` of a
byte's low and high four bits, and `L` is linear over GF(2)). With
`N = a • i² + a • i • k + k²`, the inverse of `x` is
`(i / N) • A + (a • i + k) / N`, and with `j = i + k`

* `io = 1 / (1 / i + a / k) + j` is `N / (a • i + k)`, and
* `jo = 1 / (1 / j + a / k) + i` is `N / (a • i + a • k + k)`,

each two lookups in the tables `inv` (`1 / ·`) and `inva` (`a / ·`) of the
subfield, in which `1 / 0` is `0x80`, an index that selects 0 (`invert`). The
inverse of `x`, and so the S-box of `x`, is linear in `1 / io` and
`1 / jo`: the S-box of `x` less `0x63`, and twice it, each as `L` of it, are
the XOR of a lookup by `io` and one by `jo` (`sb1u` and `sb1t`, `sb2u` and
`sb2t`), and the S-box itself less `0x63` that of `sbou` and `sbot`.

A round (`round`) is the next round key as `L` of it plus `L 0x63`
(`keyx`: `keyHi` has `L 0x63` in every byte), `invert`, and `mix`: with
`S` the bytes `L (sbox x − 0x63)` and `r` the rotation of each column by
a byte, ShiftRows and MixColumns of them are `X ⊕ r X ⊕ r³ S'` for
`S' = ShiftRows S` and `X = 2 • S' ⊕ r S'`, the permutations being lookups
by constant indices (`sr`, `rsr`, `r3sr`, `rot`). The first round key is
added to the block as `L` of each, in which the two `L 0x63` cancel; the
last round (`last`) has no MixColumns, and gives the bytes themselves.

Only `x0`, `x1`, `x6`, `v0`–`v6` and `v16`–`v31` are written.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Vperm

open VG.AArch64 VG.Impl.Tbl.AArch64 VG.Impl.Aes.Vperm

/-- The static that holds the tables. -/
def tabName : String := "VG_AES_VPERM"

/-- The static's vectors: vector `j` is loaded into `treg j`, `v16`–`v31`
in this order. -/
def tabVecs : List (BitVec 128) :=
  [mask, inv, inva, sb1u, sb1t, sb2u, sb2t, sr, rsr, r3sr, rot, keyLo, keyHi, sbou, sbot, c63]

def tabVec (j : Nat) : BitVec 128 := tabVecs.getD j 0

/-- The static's words: vector `j` at bytes `16 j` to `16 j + 15`. -/
def tabWords : List (BitVec 64) :=
  (List.range 32).map fun i => (tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64

/-- Vector `j` of the static, at `x6`, into `treg j`. -/
def tld (j : Nat) : Instr := .ldrqTbl (treg j) .x6 (16 * j) tabName tabWords

/-- The tables into `v16`–`v31`, loaded from the static, whose address is
in `x6`. -/
def setup : List Instr := ([.adrSym .x6 tabName] : List Instr) ++ (List.range 16).map tld

/-- `d := L d ⊕ L 0x63`, through `t`. -/
def keyx (d t : VReg) : List Instr :=
  [.vop (.logic .and t d .v16), .vop (.shift .ushr .b16 d d 4), .vop (.tbl t .v27 t),
    .vop (.tbl d .v28 d), .vop (.logic .eor d d t)]

/-- `io` and `jo` of the bytes of `v0`, into `v2` and `v3`. -/
def invert : List Instr :=
  [.vop (.logic .and .v1 .v0 .v16), .vop (.shift .ushr .b16 .v0 .v0 4), .vop (.tbl .v2 .v18 .v1),
    .vop (.logic .eor .v1 .v1 .v0), .vop (.tbl .v3 .v17 .v0), .vop (.tbl .v4 .v17 .v1),
    .vop (.logic .eor .v3 .v3 .v2), .vop (.logic .eor .v4 .v4 .v2), .vop (.tbl .v2 .v17 .v3),
    .vop (.tbl .v3 .v17 .v4), .vop (.logic .eor .v2 .v2 .v1), .vop (.logic .eor .v3 .v3 .v0)]

/-- The S-box at `io` and `jo` (`v2` and `v3`), ShiftRows and MixColumns,
and the round key in `v5`, into `v0`. -/
def mix : List Instr :=
  [.vop (.tbl .v0 .v19 .v2), .vop (.tbl .v1 .v20 .v3), .vop (.tbl .v2 .v21 .v2), .vop (.tbl .v3 .v22 .v3),
    .vop (.logic .eor .v0 .v0 .v1), .vop (.logic .eor .v2 .v2 .v3), .vop (.tbl .v1 .v2 .v23),
    .vop (.tbl .v3 .v0 .v24), .vop (.tbl .v0 .v0 .v25), .vop (.logic .eor .v1 .v1 .v3),
    .vop (.logic .eor .v0 .v0 .v5), .vop (.tbl .v3 .v1 .v26), .vop (.logic .eor .v0 .v0 .v1),
    .vop (.logic .eor .v0 .v0 .v3)]

/-- The S-box at `io` and `jo` (`v2` and `v3`), ShiftRows, and the round
key in `v5`, into `v0`. -/
def last : List Instr :=
  [.vop (.tbl .v0 .v29 .v2), .vop (.tbl .v1 .v30 .v3), .vop (.logic .eor .v0 .v0 .v1),
    .vop (.tbl .v0 .v0 .v23), .vop (.logic .eor .v5 .v5 .v31), .vop (.logic .eor .v0 .v0 .v5)]

/-- The block in `v0` and the first round key, as `L` of their XOR, and one
round fewer left in `x1`. -/
def first : List Instr :=
  ([.ldrq .v5 .x0 0] : List Instr) ++ keyx .v0 .v1 ++ keyx .v5 .v6 ++
    ([.vop (.logic .eor .v0 .v0 .v5), .subImm .x .x1 .x1 1] : List Instr)

/-- A full round, with the next round key: `x0` to it, and one round fewer
left in `x1`. -/
def round : List Instr :=
  ([.addImm .x .x0 .x0 16, .ldrq .v5 .x0 0] : List Instr) ++ keyx .v5 .v6 ++ invert ++ mix ++
    ([.subImm .x .x1 .x1 1] : List Instr)

/-- The rounds: AddRoundKey, `x1 − 1` full rounds, and the last. -/
def rounds : Prog isa :=
  .seq (.block first)
    (.seq (.loop (.block round) (.nonzero .x .x1))
      (.block (([.ldrq .v5 .x0 16] : List Instr) ++ invert ++ last)))

/-- `v0 := CIPHER(v0)`, with the key schedule at `x0` and `x1` rounds. -/
def core : Prog isa := .seq (.block setup) rounds

/-!
## Decryption

`Dec.core`: `v0 := INVCIPHER(v0)`, FIPS 197's inverse cipher with the same
key schedule, read from its last round key down.

The inverse S-box is the inverse of the affine map, then the inversion: the
state is kept as the bytes `D x`, `L` of the affine map's inverse of `x`
(`dl` and `dh`, of a byte's low and high four bits: `D` is linear but for
`D 0`), whose `io` and `jo` (`invert`) give the inverse S-box of `x`
(`dbou`, `dbot`) and, less `D 0`, `D` of its products by InvMixColumns'
`0e`, `0b`, `0d` and `09` (`x0u` … `x3t`), each permuted by InvShiftRows
and the rotation of the columns that brings it to its place (`p0` … `p3`).
A round key is added before InvMixColumns: `D` of its four products (`y0l`
… `y3h`, by its low and high four bits, the first with `D 0`), rotated
alike (`rot1`, `rot2`, `rot3`), are XORed in (`key`).

The tables that do not fit `v16`–`v30` are loaded as they are used, through
`v1` and `v2`. Only `x0`, `x1`, `x6`, `v0`–`v7` and `v16`–`v30` are
written.
-/

namespace Dec

open VG.Impl.Aes.Vperm.Dec

/-- The static that holds the tables of the decryption. -/
def tabName : String := "VG_AES_VPERM_DEC"

/-- The static's vectors: the first fifteen are loaded into `v16`–`v30`,
in this order. -/
def tabVecs : List (BitVec 128) :=
  [mask, inv, inva, x0u, x0t, x1u, x1t, x2u, x2t, x3u, x3t, p0, p1, p2, p3,
    y0l, y0h, y1l, y1h, y2l, y2h, y3l, y3h, rot, rot2, rot3, dl, dh, dbou, dbot]

def tabVec (j : Nat) : BitVec 128 := tabVecs.getD j 0

/-- The static's words: vector `j` at bytes `16 j` to `16 j + 15`. -/
def tabWords : List (BitVec 64) :=
  (List.range 60).map fun i => (tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64

/-- Vector `j` of the static, at `x6`, into `r`. -/
def tld (r : VReg) (j : Nat) : Instr := .ldrqTbl r .x6 (16 * j) tabName tabWords

/-- The tables into `v16`–`v30`, loaded from the static, whose address is
in `x6`, after `x0` is moved to the last round key (through `x6`). -/
def setup : List Instr :=
  ([.lsl .x .x6 .x1 4, .add .x .x0 .x0 .x6, .adrSym .x6 tabName] : List Instr) ++
    (List.range 15).map fun j => tld (treg j) j

/-- The products of the round key (its low four bits in `v6`, its high four
in `v5`) by constant `n`: vectors `jl` and `jh` of the static at them,
XORed, into `d`. -/
def keyTerm (d : VReg) (jl jh : Nat) : List Instr :=
  [tld .v1 jl, tld .v2 jh, .vop (.tbl .v1 .v1 .v6), .vop (.tbl .v2 .v2 .v5), .vop (.logic .eor d .v1 .v2)]

/-- `v1`, its columns rotated by vector `jp` of the static, XORed into `v7`. -/
def keyRot (jp : Nat) : List Instr :=
  [tld .v2 jp, .vop (.tbl .v1 .v1 .v2), .vop (.logic .eor .v7 .v7 .v1)]

/-- `D` of InvMixColumns of the round key in `v5`, with `D 0`, into `v7`. -/
def key : List Instr :=
  ([.vop (.logic .and .v6 .v5 .v16), .vop (.shift .ushr .b16 .v5 .v5 4)] : List Instr) ++
    keyTerm .v7 15 16 ++ keyTerm .v1 17 18 ++ keyRot 23 ++ keyTerm .v1 19 20 ++ keyRot 24 ++
    keyTerm .v1 21 22 ++ keyRot 25

/-- The products of the inverse S-box at `io` and `jo` (`v2` and `v3`),
InvShiftRows and InvMixColumns, and the round key's part in `v7`, into
`v0`. -/
def mix : List Instr :=
  [.vop (.tbl .v0 .v19 .v2), .vop (.tbl .v1 .v20 .v3), .vop (.logic .eor .v0 .v0 .v1),
    .vop (.tbl .v0 .v0 .v27),
    .vop (.tbl .v1 .v21 .v2), .vop (.tbl .v4 .v22 .v3), .vop (.logic .eor .v1 .v1 .v4),
    .vop (.tbl .v1 .v1 .v28),
    .vop (.tbl .v4 .v23 .v2), .vop (.tbl .v5 .v24 .v3), .vop (.logic .eor .v4 .v4 .v5),
    .vop (.tbl .v4 .v4 .v29),
    .vop (.tbl .v5 .v25 .v2), .vop (.tbl .v6 .v26 .v3), .vop (.logic .eor .v5 .v5 .v6),
    .vop (.tbl .v5 .v5 .v30),
    .vop (.logic .eor .v0 .v0 .v1), .vop (.logic .eor .v4 .v4 .v5), .vop (.logic .eor .v0 .v0 .v7),
    .vop (.logic .eor .v0 .v0 .v4)]

/-- The block in `v0` and the last round key, as `D` of their XOR, and one
round fewer left in `x1`. -/
def first : List Instr :=
  [.ldrq .v5 .x0 0, .vop (.logic .eor .v0 .v0 .v5), tld .v2 26, tld .v3 27,
    .vop (.logic .and .v1 .v0 .v16), .vop (.shift .ushr .b16 .v0 .v0 4), .vop (.tbl .v1 .v2 .v1),
    .vop (.tbl .v0 .v3 .v0), .vop (.logic .eor .v0 .v0 .v1), .subImm .x .x1 .x1 1]

/-- A full round, with the round key before: `x0` to it, and one round
fewer left in `x1`. -/
def round : List Instr :=
  ([.subImm .x .x0 .x0 16, .ldrq .v5 .x0 0] : List Instr) ++ key ++ invert ++ mix ++
    ([.subImm .x .x1 .x1 1] : List Instr)

/-- The inverse S-box at `io` and `jo` (`v2` and `v3`), InvShiftRows, and
the round key in `v5`, into `v0`. -/
def last : List Instr :=
  [tld .v0 28, tld .v1 29, .vop (.tbl .v0 .v0 .v2), .vop (.tbl .v1 .v1 .v3),
    .vop (.logic .eor .v0 .v0 .v1), .vop (.tbl .v0 .v0 .v27), .vop (.logic .eor .v0 .v0 .v5)]

/-- The rounds: AddRoundKey, `x1 − 1` full rounds, and the last. -/
def rounds : Prog isa :=
  .seq (.block first)
    (.seq (.loop (.block round) (.nonzero .x .x1))
      (.block (([.subImm .x .x0 .x0 16, .ldrq .v5 .x0 0] : List Instr) ++ invert ++ last)))

/-- `v0 := INVCIPHER(v0)`, with the key schedule at `x0` and `x1` rounds. -/
def core : Prog isa := .seq (.block setup) rounds

end Dec

end VG.Impl.Aes.AArch64.Vperm
