module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq

/-!
# A single-block SEED core on PPC64LE

The serial modes (CBC and CFB encryption, OFB) take one block a step, but
the blocks function (`Modes.lean`) computes sixteen lanes whatever the
number of blocks. `core` enciphers the one block of its buffer as RFC 4269
describes, the halves in general-purpose registers, each `G`'s S-boxes on the
vector unit.

SEED's S-boxes `S1` and `S2` (`Spec.Seed.s0`, `s1`) are `A · x^247 ⊕ c` and
`A' · x^251 ⊕ c'` in their field, and `x^247` and `x^251` are powers of two of
the inverse, which are linear: each is affine-equivalent to the AES S-box,
`S(x) = A_out(S_AES(A_in(x)))`, with the same `A_in` (the fields'
isomorphism) and its own `A_out`. An affine map on a byte is the XOR of a
table of its low nibble and one of its high nibble, which `vperm` looks up
for every byte of a register at once, its index's bit 4 choosing between two
tables. So `gFn` splits `G`'s word into nibbles (through the mask
`0x0f0f0f0f` in `r12`), moves them to vector registers (`mtvsrd`), looks
up `A_in`, applies `vsbox` (the AES S-box on every byte), splits the result
again, looks up `S1`'s `A_out` or, for the bytes `X1` and `X3`, `S2`'s
(`selOut`), then broadcasts each byte to a word (`vperm` by `bidx`), masks the
words with `G`'s masks (`mask`) and XORs them together (`vsldoi`). Every
index is a vector register's byte; no address or branch depends on the key
or the data.

The block's words (big-endian, `lwbrx`) are in `r4`, `r6`, `r7`, `r8`; the
round keys are read from the schedule at `r3`; `F` works in `r9` and `r10`,
`G` in `r0` and `r11`. The halves trade registers every round, which the
rounds, unrolled, follow. The tables are in `v8`–`v16`, loaded from the
static `tableSym` (`lxvd2xTbl`, its address in `r10`). The core writes only
`r0`, `r4`, `r6`–`r12`, `v0`, `v1` and `v8`–`v16`, and the link register
(`adrSym`), which the modes restore. Its slots are those of the blocks
function's core on one block (`dirCore`, `Modes.lean`), so that the modes over either take
the same scratch buffer (`[u64; 144]`).
-/

@[expose] public section

namespace VG.Impl.Seed.PPC64LE

/-- The modes' buffer's block (`Modes.lean`), after the blocks function's
working space. -/
def bufSlot : Nat := 136

end VG.Impl.Seed.PPC64LE

namespace VG.Impl.Seed.PPC64LE.Serial

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)

/-! ## The tables -/

def inLo : Vector (BitVec 8) 16 :=
  #v[0x00, 0x01, 0x19, 0x18, 0x5a, 0x5b, 0x43, 0x42, 0x6b, 0x6a, 0x72, 0x73, 0x31, 0x30, 0x28, 0x29]
def inHi : Vector (BitVec 8) 16 :=
  #v[0x00, 0xf4, 0xcc, 0x38, 0x82, 0x76, 0x4e, 0xba, 0x06, 0xf2, 0xca, 0x3e, 0x84, 0x70, 0x48, 0xbc]
def out0Lo : Vector (BitVec 8) 16 :=
  #v[0xe7, 0x9b, 0x43, 0x3f, 0xfc, 0x80, 0x58, 0x24, 0x57, 0x2b, 0xf3, 0x8f, 0x4c, 0x30, 0xe8, 0x94]
def out0Hi : Vector (BitVec 8) 16 :=
  #v[0x00, 0x5f, 0x69, 0x36, 0xff, 0xa0, 0x96, 0xc9, 0x8a, 0xd5, 0xe3, 0xbc, 0x75, 0x2a, 0x1c, 0x43]
def out1Lo : Vector (BitVec 8) 16 :=
  #v[0x2b, 0x27, 0x60, 0x6c, 0x6f, 0x63, 0x24, 0x28, 0xd6, 0xda, 0x9d, 0x91, 0x92, 0x9e, 0xd9, 0xd5]
def out1Hi : Vector (BitVec 8) 16 :=
  #v[0x00, 0x2e, 0x2a, 0x04, 0x7e, 0x50, 0x54, 0x7a, 0x12, 0x3c, 0x38, 0x16, 0x6c, 0x42, 0x46, 0x68]
/-- Bit 4 of the index of the bytes of `S2` (`X1`, `X3`), in the high doubleword's low word. -/
def selOut : Vector (BitVec 8) 16 := #v[0, 0, 0, 0, 0x10, 0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Byte `Xi`'s image broadcast to word `i`. -/
def bidx : Vector (BitVec 8) 16 := #v[7, 7, 7, 7, 6, 6, 6, 6, 5, 5, 5, 5, 4, 4, 4, 4]
/-- `G`'s masks: word `i`, byte `j` from the least significant, `m_{(i+j) mod 4}`. -/
def mask : Vector (BitVec 8) 16 := #v[0x3f, 0xcf, 0xf3, 0xfc, 0xfc, 0x3f, 0xcf, 0xf3, 0xf3, 0xfc, 0x3f, 0xcf, 0xcf, 0xf3, 0xfc, 0x3f]

/-- The doubleword of bytes `t[8 h] … t[8 h + 7]`, the first the most
significant, as `lxvd2xTbl` places a table's words in a register's
doublewords (element 0, the most significant byte, first). -/
def dword (t : Vector (BitVec 8) 16) (h : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).foldl (fun a j => a + (t.getD (8 * h + j) 0).toNat * 2 ^ (8 * (7 - j))) 0)

/-- The tables, in the order of `treg`. -/
def tables : List (Vector (BitVec 8) 16) := [inLo, inHi, out0Lo, out1Lo, out0Hi, out1Hi, selOut, bidx, mask]

def tableWords : List (BitVec 64) := tables.flatMap fun t => [dword t 0, dword t 1]

def tableSym : String := "VG_SEED_PPC64LE_AFFINE"

/-- The vector register of table `k`. -/
def treg (k : Nat) : VReg := [VReg.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16].getD k .v8

/-- The tables to their registers, and the mask `0x0f0f0f0f` to `r12`. -/
def loadTables : List Instr :=
  .adrSym .r10 tableSym :: (List.range 9).flatMap (fun k =>
    [.li .r11 (16 * k), .lxvd2xTbl (treg k) .r10 .r11 tableSym tableWords]) ++
  [.lis .r12 0x0f0f, .ori .r12 .r12 0x0f0f]

/-! ## G -/

/-- The nibbles of `x`'s low word: the low ones to `r0`, the high ones to `r11`. -/
def nibbles (x : Reg) : List Instr := [.logic .and .r0 x .r12, .lsr .w .r11 x 4, .logic .and .r11 .r11 .r12]

/-- `x := G(x)`. -/
def gFn (x : Reg) : List Instr :=
  nibbles x ++
  [.mtvsrd .v0 .r0, .mtvsrd .v1 .r11,
   .vop (.perm .v0 .v8 .v8 .v0), .vop (.perm .v1 .v9 .v9 .v1), .vop (.logic .xor .v0 .v0 .v1),
   .vop (.sbox .v0 .v0), .mfvsrd x .v0] ++
  nibbles x ++
  [.mtvsrd .v0 .r0, .mtvsrd .v1 .r11,
   .vop (.logic .or .v0 .v0 .v14), .vop (.logic .or .v1 .v1 .v14),
   .vop (.perm .v0 .v10 .v11 .v0), .vop (.perm .v1 .v12 .v13 .v1), .vop (.logic .xor .v0 .v0 .v1),
   .vop (.perm .v0 .v0 .v0 .v15), .vop (.logic .and .v0 .v0 .v16),
   .vop (.sldoi .v1 .v0 .v0 8), .vop (.logic .xor .v0 .v0 .v1),
   .vop (.sldoi .v1 .v0 .v0 4), .vop (.logic .xor .v0 .v0 .v1), .mfvsrd x .v0]

/-! ## A round -/

/-- `L ^= F(K_j, R)`, the left half in `p0`, `p1` and the right in `q0`, `q1`. -/
def fRound (p0 p1 q0 q1 : Reg) (j : Nat) : List Instr :=
  [.load .w .r9 .r3 (8 * j), .load .w .r10 .r3 (8 * j + 4),
   .logic .xor .r9 .r9 q0, .logic .xor .r10 .r10 q1, .logic .xor .r10 .r9 .r10] ++
  gFn .r10 ++ [.add .r9 .r10 .r9] ++ gFn .r9 ++ [.add .r10 .r9 .r10] ++ gFn .r10 ++
  [.add .r9 .r10 .r9, .logic .xor p0 p0 .r9, .logic .xor p1 p1 .r10]

/-- Round `j`: the halves in `r4`, `r6` and `r7`, `r8` alternately. -/
def round (j : Nat) : List Instr :=
  if j % 2 = 0 then fRound .r4 .r6 .r7 .r8 j else fRound .r7 .r8 .r4 .r6 j

/-- The sixteen rounds. -/
def rounds : List Instr := (List.range 16).flatMap round

/-! ## The block -/

/-- The block's words to `r4`, `r6`, `r7`, `r8`. -/
def loadBlock : List Instr :=
  [.li .r0 (8 * bufSlot), .loadRev .w .r4 sb .r0, .li .r0 (8 * bufSlot + 4), .loadRev .w .r6 sb .r0,
   .li .r0 (8 * bufSlot + 8), .loadRev .w .r7 sb .r0, .li .r0 (8 * bufSlot + 12), .loadRev .w .r8 sb .r0]

/-- The output words, `r7`, `r8`, `r4`, `r6` after the sixteen rounds, back to the block. -/
def storeBlock : List Instr :=
  [.li .r0 (8 * bufSlot), .storeRev .w .r7 sb .r0, .li .r0 (8 * bufSlot + 4), .storeRev .w .r8 sb .r0,
   .li .r0 (8 * bufSlot + 8), .storeRev .w .r4 sb .r0, .li .r0 (8 * bufSlot + 12), .storeRev .w .r6 sb .r0]

/-- The single-block core, for encryption (the schedule's round keys in order). -/
def core : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := .block (loadTables ++ loadBlock ++ rounds ++ storeBlock)
  slots := bufSlot + 2
  total := bufSlot + 8
  buf := bufSlot
  G := 1
  bw := 4

end VG.Impl.Seed.PPC64LE.Serial
