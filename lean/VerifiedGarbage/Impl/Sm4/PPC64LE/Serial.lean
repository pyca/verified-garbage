module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Layers

/-!
# A single-block SM4 core on PPC64LE

The serial modes (CBC and CFB encryption, OFB) take one block a step, but
the bitsliced core (`Modes.lean`) costs a whole batch of sixteen for each.
`core` enciphers the one block of its buffer, a word at a time, as the
standard describes, its S-boxes on the vector unit.

SM4's S-box is affine-equivalent to the AES S-box (`Impl/Sm4/Circuit.lean`):
`S(x) = A_out(S_AES(A_in(x)))` for affine maps `A_in` and `A_out` on
bytes. An affine map on a byte is the XOR of a table of its low nibble and
a table of its high nibble, each of sixteen bytes, which `vperm` looks up
for every byte of a register at once (`inLo`, `inHi`, `outLo`, `outHi`, the
constants folded into the low tables). So `tau` splits the round's word into
its nibbles in general-purpose registers (`r10`, `r11`, through the mask
`0x0f0f0f0f` in `r12`), moves each to a vector register (`mtvsrd`), looks
them up and XORs them, applies `vsbox` (the AES S-box on every byte), and
does the same with `A_out`'s tables, before moving the word back
(`mfvsrd`). Every index is a vector register's byte; no address or branch
depends on the key or the data.

The block's words (big-endian, `lwbrx`) are in `wordReg 0 … 3`
(`r4`, `r6`, `r7`, `r8`), the round's word in `r9`, the round keys are read
from the schedule at `r3`, and the tables are in `v12`–`v15`, loaded from the
static `tableSym` (`lxvd2xTbl`, its address in `r10`). The core writes
only `r0`, `r4`, `r6`–`r12`, `v0`, `v1` and `v12`–`v15`, and the link
register (`adrSym`), which the modes restore.

Its slots are the bitsliced core's (`Modes.lean`), its buffer that core's
first block (`tailSlot`), so that the modes over either take the same
scratch buffer (`[u64; 408]`).
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE.Serial

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (mov sb)

/-! ## The tables -/

def inLo : Vector (BitVec 8) 16 :=
  #v[0x3e, 0xb2, 0x0e, 0x82, 0xbb, 0x37, 0x8b, 0x07, 0xa1, 0x2d, 0x91, 0x1d, 0x24, 0xa8, 0x14, 0x98]
def inHi : Vector (BitVec 8) 16 :=
  #v[0x00, 0xdc, 0x2e, 0xf2, 0xc5, 0x19, 0xeb, 0x37, 0x08, 0xd4, 0x26, 0xfa, 0xcd, 0x11, 0xe3, 0x3f]
def outLo : Vector (BitVec 8) 16 :=
  #v[0x6c, 0xd4, 0xa6, 0x1e, 0x52, 0xea, 0x98, 0x20, 0x0b, 0xb3, 0xc1, 0x79, 0x35, 0x8d, 0xff, 0x47]
def outHi : Vector (BitVec 8) 16 :=
  #v[0x00, 0xe0, 0x50, 0xb0, 0x9d, 0x7d, 0xcd, 0x2d, 0xc0, 0x20, 0x90, 0x70, 0x5d, 0xbd, 0x0d, 0xed]

/-- The doubleword of bytes `t[8 h] … t[8 h + 7]`, the first the most
significant, as `lxvd2xTbl` places a table's words in a register's
doublewords (element 0, the most significant byte, first). -/
def dword (t : Vector (BitVec 8) 16) (h : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).foldl (fun a j => a + (t.getD (8 * h + j) 0).toNat * 2 ^ (8 * (7 - j))) 0)

/-- The four tables, two doublewords each. -/
def tableWords : List (BitVec 64) :=
  [inLo, inHi, outLo, outHi].flatMap fun t => [dword t 0, dword t 1]

def tableSym : String := "VG_SM4_PPC64LE_AFFINE"

/-- The vector register of table `k`: `inLo`, `inHi`, `outLo`, `outHi`. -/
def treg (k : Nat) : VReg := [VReg.v12, .v13, .v14, .v15].getD k .v12

/-- The tables to `v12`–`v15`, and the mask `0x0f0f0f0f` to `r12`. -/
def loadTables : List Instr :=
  .adrSym .r10 tableSym :: (List.range 4).flatMap (fun k =>
    [.li .r11 (16 * k), .lxvd2xTbl (treg k) .r10 .r11 tableSym tableWords]) ++
  [.lis .r12 0x0f0f, .ori .r12 .r12 0x0f0f]

/-! ## A round -/

/-- The block's word `i mod 4`. -/
def wordReg (i : Nat) : Reg := [Reg.r4, .r6, .r7, .r8].getD (i % 4) .r4

/-- The affine map of the tables `lo` and `hi` on the bytes of `r9`, back to
`r9`. -/
def affine (lo hi : VReg) : List Instr :=
  [.logic .and .r10 .r9 .r12, .lsr .w .r11 .r9 4, .logic .and .r11 .r11 .r12,
   .mtvsrd .v0 .r10, .mtvsrd .v1 .r11,
   .vop (.perm .v0 lo lo .v0), .vop (.perm .v1 hi hi .v1), .vop (.logic .xor .v0 .v0 .v1)]

/-- SM4's S-box on the bytes of `r9` (`τ`). -/
def tau : List Instr :=
  affine (treg 0) (treg 1) ++ [.vop (.sbox .v0 .v0), .mfvsrd .r9 .v0] ++
  affine (treg 2) (treg 3) ++ [.mfvsrd .r9 .v0]

/-- `r11 := L(r9)` (`r10` its scratch). -/
def linear : List Instr :=
  [.rotr .w .r10 .r9 30, .logic .xor .r11 .r9 .r10,
   .rotr .w .r10 .r9 22, .logic .xor .r11 .r11 .r10,
   .rotr .w .r10 .r9 14, .logic .xor .r11 .r11 .r10,
   .rotr .w .r10 .r9 8, .logic .xor .r11 .r11 .r10]

/-- Round `i`: `X_i := X_i ⊕ T(X_{i+1} ⊕ X_{i+2} ⊕ X_{i+3} ⊕ rk_i)`. -/
def round (i : Nat) : List Instr :=
  [.load .w .r9 .r3 (4 * i), .logic .xor .r9 .r9 (wordReg (i + 1)),
   .logic .xor .r9 .r9 (wordReg (i + 2)), .logic .xor .r9 .r9 (wordReg (i + 3))] ++
  tau ++ linear ++ [.logic .xor (wordReg i) (wordReg i) .r11]

/-! ## The block -/

/-- The block's big-endian words to `wordReg 0 … 3`. -/
def loadBlock : List Instr :=
  (List.range 4).flatMap fun i => [.li .r0 (8 * tailSlot + 4 * i), .loadRev .w (wordReg i) sb .r0]

/-- `X₃₅, X₃₄, X₃₃, X₃₂` (`wordReg 3 … 0`) back to the block. -/
def storeBlock : List Instr :=
  (List.range 4).flatMap fun i => [.li .r0 (8 * tailSlot + 4 * i), .storeRev .w (wordReg (3 - i)) sb .r0]

/-- The 32 rounds. -/
def rounds : List Instr := (List.range 32).flatMap round

/-- The single-block core, for the encryption direction (the schedule's
round keys in order). -/
def core : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := .block (loadTables ++ loadBlock ++ rounds ++ storeBlock)
  slots := slots
  total := slots + 6
  buf := tailSlot
  G := 1
  bw := 4

end VG.Impl.Sm4.PPC64LE.Serial
