module

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

open VG.AArch64 VG.Impl.Tbl.AArch64

/-- The static that holds the tables. -/
def tabName : String := "VG_AES_VPERM"

/-- `0x0f` in every byte: the mask of a byte's low four bits. -/
def mask : BitVec 128 := 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
/-- `1 / ·` in the subfield, `0x80` for 0. -/
def inv : BitVec 128 := 0x040703090a0b0c020e05060f0d080180
/-- `a / ·` in the subfield, `0x80` for 0. -/
def inva : BitVec 128 := 0x0f09060305070e040a0d0b080c010280
/-- `L (sbox x ⊕ 0x63)`, as the XOR of `sb1u` at `io` and `sb1t` at `jo`. -/
def sb1u : BitVec 128 := 0x62cdaf73dc8e43fdbe309fec11215200
def sb1t : BitVec 128 := 0xf12cdd518c4569147d38e5b4a098c900
/-- `L (2 • (sbox x ⊕ 0x63))`, as the XOR of `sb2u` at `io` and `sb2t` at `jo`. -/
def sb2u : BitVec 128 := 0x05dbde24fac219e6ff3de3c7211c3800
def sb2t : BitVec 128 := 0xce03cd66abc3c0a565a66b0da80e6800
/-- ShiftRows, as the indices of a `tbl`: byte `t` of the result is byte
`t mod 4 + 4 ((t / 4 + t mod 4) mod 4)` of the state. -/
def sr : BitVec 128 := 0x0b06010c07020d08030e09040f0a0500
/-- ShiftRows, then each column rotated by one byte. -/
def rsr : BitVec 128 := 0x0c0b06010807020d04030e09000f0a05
/-- ShiftRows, then each column rotated by three bytes. -/
def r3sr : BitVec 128 := 0x06010c0b020d08070e0904030a05000f
/-- Each column rotated by one byte. -/
def rot : BitVec 128 := 0x0c0f0e0d080b0a090407060500030201
/-- `L` of a byte's low four bits. -/
def keyLo : BitVec 128 := 0x34350302e4e5d3d2e6e7d1d036370100
/-- `L` of a byte's high four bits, XORed with `L 0x63`. -/
def keyHi : BitVec 128 := 0x45fe3e85fa41813a8d36f64d328949f2
/-- `sbox x ⊕ 0x63`, as the XOR of `sbou` at `io` and `sbot` at `jo`. -/
def sbou : BitVec 128 := 0xa5d17490e41ecf8e415f2bbb356afa00
def sbot : BitVec 128 := 0x6e8be5f7129318647cef0afd99768100
/-- `0x63` in every byte. -/
def c63 : BitVec 128 := 0x63636363636363636363636363636363

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

end VG.Impl.Aes.AArch64.Vperm
