module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Layers

/-!
# A single-block Camellia core on PPC64LE

The serial modes (CBC and CFB encryption, OFB) take one block a step, but
the bitsliced core (`Modes.lean`) costs a whole batch of eight for each.
`core` enciphers the one block of its buffer as the standard describes, the
two halves `D1` and `D2` in `r6` and `r7`, each round's S-boxes on the
vector unit.

Camellia's `SBOX1` is affine-equivalent to the AES S-box
(`Impl/Camellia/Circuit.lean`): `SBOX1(x) = A_out(S_AES(A_in(x)))`, and so
are `SBOX2`, `SBOX3` and `SBOX4`, whose rotations compose with `A_out` or
`A_in`. An affine map on a byte is the XOR of a table of its low nibble and
one of its high nibble, of sixteen bytes each, which `vperm` looks up for
every byte of a register at once; its index's bit 4 chooses between two
tables. So `sLayer` splits the round's eight bytes into their nibbles
(through the mask `0x0f0f…` in `r12`), moves them to vector registers
(`mtvsrd`), sets bit 4 of the bytes of `SBOX4` (`selIn`), looks up `A_in`'s
tables or those of `A_in ∘ rotl 1`, applies `vsbox` (the AES S-box on every
byte), splits the result again, looks up `A_out`'s tables or those of
`rotl 1 ∘ A_out` (for `SBOX2`, `selOut`) and those of `rotl 7 ∘ A_out`, and
keeps the latter for the bytes of `SBOX3` (`vsel`, `mask36`). `pFn` is the
P-function on the two 32-bit halves, by rotations. Every index is a vector
register's byte, and the only branch is on the number of rounds (`r28`);
no address depends on the key or the data.

The subkeys are read, big-endian, from the schedule at `r3`, in its order
(`Spec.Camellia.scheduleWords`); the block is the buffer's first
(`tailSlot`), and the tables are in `v7`–`v19`, loaded from the static
`tableSym` (`lxvd2xTbl`, its address in `r10`). The core writes only `r0`,
`r4`, `r6`–`r12`, `v0`–`v3` and `v7`–`v19`, and the link register
(`adrSym`), which the modes restore. Its slots are the bitsliced core's, so
that the modes over either take the same scratch buffer (`[u64; 422]`).
-/

@[expose] public section

namespace VG.Impl.Camellia.PPC64LE.Serial

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)

/-! ## The tables -/

def inLo : Vector (BitVec 8) 16 :=
  #v[0x45, 0xe8, 0x40, 0xed, 0x2e, 0x83, 0x2b, 0x86, 0x4b, 0xe6, 0x4e, 0xe3, 0x20, 0x8d, 0x25, 0x88]
def in4Lo : Vector (BitVec 8) 16 :=
  #v[0x45, 0x40, 0x2e, 0x2b, 0x4b, 0x4e, 0x20, 0x25, 0x14, 0x11, 0x7f, 0x7a, 0x1a, 0x1f, 0x71, 0x74]
def inHi : Vector (BitVec 8) 16 :=
  #v[0x00, 0x51, 0xf1, 0xa0, 0x8a, 0xdb, 0x7b, 0x2a, 0x09, 0x58, 0xf8, 0xa9, 0x83, 0xd2, 0x72, 0x23]
def in4Hi : Vector (BitVec 8) 16 :=
  #v[0x00, 0xf1, 0x8a, 0x7b, 0x09, 0xf8, 0x83, 0x72, 0xad, 0x5c, 0x27, 0xd6, 0xa4, 0x55, 0x2e, 0xdf]
def outLo : Vector (BitVec 8) 16 :=
  #v[0x3c, 0xcc, 0xcf, 0x3f, 0x32, 0xc2, 0xc1, 0x31, 0xdc, 0x2c, 0x2f, 0xdf, 0xd2, 0x22, 0x21, 0xd1]
def out2Lo : Vector (BitVec 8) 16 :=
  #v[0x78, 0x99, 0x9f, 0x7e, 0x64, 0x85, 0x83, 0x62, 0xb9, 0x58, 0x5e, 0xbf, 0xa5, 0x44, 0x42, 0xa3]
def outHi : Vector (BitVec 8) 16 :=
  #v[0x00, 0xf9, 0x86, 0x7f, 0xd7, 0x2e, 0x51, 0xa8, 0xa4, 0x5d, 0x22, 0xdb, 0x73, 0x8a, 0xf5, 0x0c]
def out2Hi : Vector (BitVec 8) 16 :=
  #v[0x00, 0xf3, 0x0d, 0xfe, 0xaf, 0x5c, 0xa2, 0x51, 0x49, 0xba, 0x44, 0xb7, 0xe6, 0x15, 0xeb, 0x18]
def out3Lo : Vector (BitVec 8) 16 :=
  #v[0x1e, 0x66, 0xe7, 0x9f, 0x19, 0x61, 0xe0, 0x98, 0x6e, 0x16, 0x97, 0xef, 0x69, 0x11, 0x90, 0xe8]
def out3Hi : Vector (BitVec 8) 16 :=
  #v[0x00, 0xfc, 0x43, 0xbf, 0xeb, 0x17, 0xa8, 0x54, 0x52, 0xae, 0x11, 0xed, 0xb9, 0x45, 0xfa, 0x06]
/-- Bit 4 of the index of the bytes of `SBOX4` (`t4`, `t7`). -/
def selIn : Vector (BitVec 8) 16 := #v[0, 0, 0, 0x10, 0, 0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Bit 4 of the index of the bytes of `SBOX2` (`t2`, `t5`). -/
def selOut : Vector (BitVec 8) 16 := #v[0, 0x10, 0, 0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The bytes of `SBOX3` (`t3`, `t6`). -/
def mask36 : Vector (BitVec 8) 16 := #v[0, 0, 0xff, 0, 0, 0xff, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The nibbles' mask. -/
def m0f : Vector (BitVec 8) 16 := Vector.replicate 16 0x0f

/-- The doubleword of bytes `t[8 h] … t[8 h + 7]`, the first the most
significant, as `lxvd2xTbl` places a table's words in a register's
doublewords (element 0, the most significant byte, first). -/
def dword (t : Vector (BitVec 8) 16) (h : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).foldl (fun a j => a + (t.getD (8 * h + j) 0).toNat * 2 ^ (8 * (7 - j))) 0)

/-- The tables, in the order of `treg`. -/
def tables : List (Vector (BitVec 8) 16) :=
  [inLo, in4Lo, inHi, in4Hi, outLo, out2Lo, outHi, out2Hi, out3Lo, out3Hi, selIn, selOut, mask36, m0f]

def tableWords : List (BitVec 64) := tables.flatMap fun t => [dword t 0, dword t 1]

def tableSym : String := "VG_CAMELLIA_PPC64LE_AFFINE"

/-- The vector register of table `k`: `v8`–`v19`, `mask36` in `v7`, and the
mask `m0f`, which goes to `r12`, in `v0`. -/
def treg (k : Nat) : VReg :=
  [VReg.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19, .v7, .v0].getD k .v0

/-- The tables to their registers, and the mask `0x0f0f…` to `r12`. -/
def loadTables : List Instr :=
  .adrSym .r10 tableSym :: (List.range 14).flatMap (fun k =>
    [.li .r11 (16 * k), .lxvd2xTbl (treg k) .r10 .r11 tableSym tableWords]) ++
  [.mfvsrd .r12 .v0]

/-! ## The F-function -/

/-- The nibbles of `r8`: the low ones to `r9`, the high ones to `r10`. -/
def nibbles : List Instr := [.logic .and .r9 .r8 .r12, .lsr .d .r10 .r8 4, .logic .and .r10 .r10 .r12]

/-- The AES S-box of `A_in` (or `A_in ∘ rotl 1`, for `SBOX4`'s bytes) of
the bytes of `r8`, back to `r8`. -/
def stage1 : List Instr :=
  nibbles ++
  [.mtvsrd .v0 .r9, .mtvsrd .v1 .r10,
   .vop (.logic .or .v0 .v0 .v18), .vop (.logic .or .v1 .v1 .v18),
   .vop (.perm .v0 .v8 .v9 .v0), .vop (.perm .v1 .v10 .v11 .v1), .vop (.logic .xor .v0 .v0 .v1),
   .vop (.sbox .v0 .v0), .mfvsrd .r8 .v0]

/-- `A_out` of the bytes of `r8` (`rotl 1 ∘ A_out` for `SBOX2`'s,
`rotl 7 ∘ A_out` for `SBOX3`'s), back to `r8`. -/
def stage2 : List Instr :=
  nibbles ++
  [.mtvsrd .v0 .r9, .mtvsrd .v1 .r10,
   .vop (.logic .or .v2 .v0 .v19), .vop (.logic .or .v3 .v1 .v19),
   .vop (.perm .v2 .v12 .v13 .v2), .vop (.perm .v3 .v14 .v15 .v3), .vop (.logic .xor .v2 .v2 .v3),
   .vop (.perm .v0 .v16 .v16 .v0), .vop (.perm .v1 .v17 .v17 .v1), .vop (.logic .xor .v0 .v0 .v1),
   .vop (.sel .v0 .v2 .v0 .v7), .mfvsrd .r8 .v0]

/-- `r8 := S(r8)`: `SBOX1 … SBOX4` on the bytes `t1 … t8` of `r8`, as `F`
applies them. -/
def sLayer : List Instr := stage1 ++ stage2

/-- `r8 := P(r8)`, on its halves `r9` (high) and `r10` (low), `r11`, `r4`
and `r0` its scratch. -/
def pFn : List Instr :=
  [.lsr .d .r9 .r8 32, .rotr .w .r10 .r8 0,
   .rotr .w .r11 .r9 8, .logic .xor .r11 .r9 .r11, .rotr .w .r4 .r9 16, .logic .xor .r11 .r11 .r4,
   .rotr .w .r4 .r10 8, .rotr .w .r0 .r10 16, .logic .xor .r4 .r4 .r0,
   .rotr .w .r0 .r10 24, .logic .xor .r4 .r4 .r0,
   .logic .xor .r11 .r11 .r4,
   .rotr .w .r0 .r9 24, .logic .xor .r10 .r9 .r0, .logic .xor .r10 .r10 .r4,
   .lsl .r11 .r11 32, .logic .or .r8 .r11 .r10]

/-- The schedule's word `k` to `r4`. -/
def loadKey (k : Nat) : List Instr := [.li .r0 (8 * k), .loadRev .d .r4 .r3 .r0]

/-- `b := b ⊕ F(a, k)`, `k` the schedule's word `w`. -/
def fRound (a b : Reg) (w : Nat) : List Instr :=
  loadKey w ++ [.logic .xor .r8 a .r4] ++ sLayer ++ pFn ++ [.logic .xor b b .r8]

/-- Six rounds, from the schedule's word `w`. -/
def six (w : Nat) : List Instr :=
  (List.range 3).flatMap fun j => fRound .r6 .r7 (w + 2 * j) ++ fRound .r7 .r6 (w + 2 * j + 1)

/-! ## FL and FLINV -/

/-- `r := FL(r, k)` (`FLINV` if `inv`), `k` the schedule's word `w`. -/
def fl (r : Reg) (w : Nat) (inv : Bool) : List Instr :=
  let lo := [Instr.logic .and .r0 .r9 .r11, .rotr .w .r0 .r0 31, .logic .xor .r10 .r10 .r0]
  let hi := [Instr.logic .or .r0 .r10 .r4, .logic .xor .r9 .r9 .r0]
  loadKey w ++ [.lsr .d .r9 r 32, .rotr .w .r10 r 0, .lsr .d .r11 .r4 32, .rotr .w .r4 .r4 0] ++
    (if inv then hi ++ lo else lo ++ hi) ++ [.lsl .r9 .r9 32, .logic .or r .r9 .r10]

/-- `D1 := FL(D1, ke)`, `D2 := FLINV(D2, ke')`, from the schedule's word `w`. -/
def flPair (w : Nat) : List Instr := fl .r6 w false ++ fl .r7 (w + 1) true

/-! ## The block -/

/-- The block's halves to `r6` and `r7`, with the prewhitening keys. -/
def loadBlock : List Instr :=
  [.li .r0 (8 * tailSlot), .loadRev .d .r6 sb .r0, .li .r0 (8 * tailSlot + 8), .loadRev .d .r7 sb .r0] ++
  loadKey 0 ++ [.logic .xor .r6 .r6 .r4] ++ loadKey 1 ++ [.logic .xor .r7 .r7 .r4]

/-- The postwhitening keys at the schedule's word `w`, and `D2 ‖ D1` back to
the block. -/
def whitening (w : Nat) : List Instr :=
  loadKey w ++ [.logic .xor .r7 .r7 .r4] ++ loadKey (w + 1) ++ [.logic .xor .r6 .r6 .r4] ++
  [.li .r0 (8 * tailSlot), .storeRev .d .r7 sb .r0, .li .r0 (8 * tailSlot + 8), .storeRev .d .r6 sb .r0]

/-- The rounds that 18 and 24 rounds share. -/
def prefixRounds : List Instr := six 2 ++ flPair 8 ++ six 10 ++ flPair 16 ++ six 18

/-- The single-block core, for encryption (the schedule's words in order),
the number of rounds in `r28`. -/
def crypt : Prog isa :=
  .seq (.block (loadTables ++ loadBlock ++ prefixRounds ++ [.subi .r9 .r28 18]))
    (.ite (.zero .d .r9) (.block (whitening 24)) (.block (flPair 24 ++ six 26 ++ whitening 32)))

def core : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := crypt
  slots := slots
  total := slots + 8
  buf := tailSlot
  G := 1
  bw := 4

end VG.Impl.Camellia.PPC64LE.Serial
