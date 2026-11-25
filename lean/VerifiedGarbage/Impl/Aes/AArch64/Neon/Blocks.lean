module

public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Sbox
public import VerifiedGarbage.Impl.Aes.AArch64.Blocks
public import VerifiedGarbage.Impl.Tbl.AArch64

/-!
# AES, eight blocks at a time, bitsliced in AdvSIMD registers, on AArch64

`vg_aes_encrypt_blocks_neon(schedule = x0, rounds = x1, data = x2, n = x3, scratch = x4)`
and `vg_aes_decrypt_blocks_neon`, for CPUs without the Cryptographic
Extension.

Bit `j` of byte `i` of block `b` is bit `b` of byte `i` of slice `j`: each
column of bytes of the eight blocks is an 8×8 bit matrix, transposed
(`ortho`). ShiftRows and the rotations of the columns' rows are then `tbl`s
of the slices, and MixColumns rotates by two rows with `rev32` of halfwords.

**The S-box's constant is in the round keys.** `{63}` in every byte goes
through ShiftRows and MixColumns unchanged (`2 + 3 + 1 + 1 = 1`), so the
round keys but the first have it added, and `subBytes` computes the S-box
without it; `invSubBytes` takes its input with it added.

**Round keys.** A slice of a round key has `00` or `ff` in byte `i`, by a bit
of the key's byte `i`: so slices `j` and `j + 4` are `tbl`s of one table
(`bitTab j`, whose byte `i` is `ff` if `i` has bit `j`) by the low and the
high halves of the key's bytes (`keyBody`). They are computed once a call.

The scratch buffer (at `x5`): a spill (0–15), the `tbl` indices (64–127),
and 128 bytes of slices for each round key, from 128.

Only `x0`, `x3`, `x4`, `x6`–`x10`, `v0`–`v7` and `v16`–`v31` are written.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Neon

open VG.AArch64
open VG.Impl.Tbl.AArch64 (const128)

/-- The round key's address, and the rounds left. -/
def kp : Reg := .x8
def cnt : Reg := .x9

/-! ## The transposes -/

/-- Exchange the high halves of the bytes of `a` with the low halves of those of `b`. -/
def swap4 (a b : VReg) : List Instr :=
  [.vop (.mov .v24 a), .vop (.shift .sli .b16 a b 4), .vop (.shift .sri .b16 b .v24 4)]

/-- Exchange the bits of `a` at the mask's positions (in `v26`) with those
of `b` `n` positions below them. -/
def swapN (n : Nat) (a b : VReg) : List Instr :=
  [.vop (.shift .ushr .b16 .v24 a n), .vop (.shift .shl .b16 .v25 b n),
   .vop (.bsel .bit a .v25 .v26), .vop (.bsel .bif b .v24 .v26)]

def maskV (v : BitVec 16) : List Instr := [.movz .w .x6 v 0, .vop (.dup .b16 .v26 .x6)]

/-- The transposes of the 8×8 bit matrices that the bytes `i` of `P 0 … P 7` make. -/
def ortho (P : Nat → VReg) : List Instr :=
  ([0, 1, 2, 3] : List Nat).flatMap (fun k => swap4 (P k) (P (k + 4))) ++
  maskV 0xCC ++ ([0, 1, 4, 5] : List Nat).flatMap (fun k => swapN 2 (P k) (P (k + 2))) ++
  maskV 0xAA ++ ([0, 2, 4, 6] : List Nat).flatMap (fun k => swapN 1 (P k) (P (k + 1)))

/-! ## `tbl` indices, in slots of the scratch buffer -/

/-- The indices whose byte `i` is `f i`. -/
def idx (f : Nat → Nat) : BitVec 128 := ofVBytes fun i => BitVec.ofNat 8 (f i)

/-- The byte, of those of the state, that ShiftRows and InvShiftRows move to byte `i`. -/
def srSrc (i : Nat) : Nat := i % 4 + 4 * ((i / 4 + i % 4) % 4)
def isrSrc (i : Nat) : Nat := i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)

/-- The byte a row further down the column of byte `i`. -/
def down1 (i : Nat) : Nat := (i % 4 + 1) % 4 + 4 * (i / 4)

def srIdx : BitVec 128 := idx srSrc
def srRotIdx : BitVec 128 := idx fun i => srSrc (down1 i)
def isrIdx : BitVec 128 := idx isrSrc
def rotIdx : BitVec 128 := idx down1

/-- The indices' offsets. -/
def srOff : Nat := 64
def srRotOff : Nat := 80
def isrOff : Nat := 96
def rotOff : Nat := 112

/-! ## The layers -/

/-- `P j := ` the `tbl` of `P j` by the indices at `off`. -/
def permute (off : Nat) (P : Nat → VReg) : List Instr :=
  .ldrq .v24 sb off :: (List.range 8).map fun j => .vop (.tbl (P j) (P j) .v24)

/-- The bytes a row down added to the slices in `B j`, which become `b`, and
in `A j` those bytes plus `b` two rows down. -/
def mcHalf (j : Nat) : List Instr :=
  [veor (B j) (B j) (A j), .vop (.rev .rev32h .v26 (B j)), veor (A j) (A j) .v26]

/-- Twice `b` added to `A j`. -/
def mcDouble : List Instr :=
  [veor (A 0) (A 0) (B 7), veor (A 1) (A 1) (B 0), veor (A 1) (A 1) (B 7), veor (A 2) (A 2) (B 1),
   veor (A 3) (A 3) (B 2), veor (A 3) (A 3) (B 7), veor (A 4) (A 4) (B 3), veor (A 4) (A 4) (B 7),
   veor (A 5) (A 5) (B 4), veor (A 6) (A 6) (B 5), veor (A 7) (A 7) (B 6)]

/-- ShiftRows and MixColumns, by the indices `srRotIdx` in `v24` and `srIdx` in `v25`. -/
def mcCore : List Instr :=
  (List.range 8).flatMap (fun j =>
    ([.vop (.tbl (A j) (B j) .v24), .vop (.tbl (B j) (B j) .v25)] : List Instr) ++ mcHalf j) ++
  mcDouble

/-- ShiftRows and MixColumns, from `B j` to `A j`: with `t` the bytes a row
down and `b = a + t`, the result is `2 b + t` plus `b` two rows down. -/
def shiftMix : List Instr := [.ldrq .v24 sb srRotOff, .ldrq .v25 sb srOff] ++ mcCore

/-- InvMixColumns is MixColumns of `a + 4 (a + a₂)`, where `a₂` is `a` two
rows down, as `{0e}, {0b}, {0d}, {09}` is `{02}, {03}, {01}, {01}` times
`{05}, {00}, {04}, {00}`: the latter product. -/
def imcPre : List Instr :=
  (List.range 8).flatMap (fun j => ([.vop (.rev .rev32h .v26 (B j)), veor (A j) (B j) .v26] : List Instr)) ++
  [veor .v26 (A 6) (A 7), veor (B 0) (B 0) (A 6), veor (B 1) (B 1) .v26, veor (B 2) (B 2) (A 0),
   veor (B 2) (B 2) (A 7), veor (B 3) (B 3) (A 1), veor (B 3) (B 3) (A 6), veor (B 4) (B 4) (A 2),
   veor (B 4) (B 4) .v26, veor (B 5) (B 5) (A 3), veor (B 5) (B 5) (A 7), veor (B 6) (B 6) (A 4),
   veor (B 7) (B 7) (A 5)]

/-- InvMixColumns, by the indices `rotIdx` in `v24`. -/
def imcCore : List Instr :=
  imcPre ++ (List.range 8).flatMap (fun j => (Instr.vop (.tbl (A j) (B j) .v24)) :: mcHalf j) ++ mcDouble

/-- InvMixColumns, from `B j` to `A j`. -/
def invMix : List Instr := .ldrq .v24 sb rotOff :: imcCore

/-- AddRoundKey, with the round key at `kp`. -/
def addRoundKey (P : Nat → VReg) : List Instr :=
  (List.range 8).flatMap fun j => [.ldrq .v24 kp (16 * j), veor (P j) (P j) .v24]

/-! ## The round keys -/

/-- The table whose byte `i` is `ff` if bit `j` of `i` is set. -/
def bitTab (j : Nat) : BitVec 128 := ofVBytes fun i => if i.testBit j then 0xFF else 0

def allBytes (b : BitVec 8) : BitVec 128 := ofVBytes fun _ => b

/-- The vectors `keySetup` makes: the indices to their slots, `keyBody`'s
tables and constants to `B j`. -/
def idxSlots : List (Nat × BitVec 128) :=
  [(srOff, srIdx), (srRotOff, srRotIdx), (isrOff, isrIdx), (rotOff, rotIdx)]

def setIdx : List Instr := idxSlots.flatMap fun (o, v) => const128 .v0 v ++ [.strq .v0 sb o]

/-- `keyBody`'s constants: the tables in `B 0 … B 3`, `0f` in every byte of
`B 4`, `63` of `B 5`, and what the next round key has added in `B 6`. -/
def keyConst : Nat → BitVec 128
  | 0 => bitTab 0 | 1 => bitTab 1 | 2 => bitTab 2 | 3 => bitTab 3
  | 4 => allBytes 0x0F | 5 => allBytes 0x63 | _ => 0

def setKeyConsts : List Instr := (List.range 7).flatMap fun k => const128 (B k) (keyConst k)

/-- The indices and constants, `x7` where the first round key's slices go,
and the round keys left. -/
def keySetup : List Instr :=
  setIdx ++ (setKeyConsts ++ ([.addImm .x .x7 sb 128, .addImm .x kp .x1 1] : List Instr))

/-- Slices `j` and `j + 4` of the round key whose bytes' halves are in `v1` and `v0`. -/
def keySlices (j : Nat) : List Instr :=
  [.vop (.tbl .v2 (B j) .v1), .strq .v2 .x7 (16 * j), .vop (.tbl .v3 (B j) .v0),
   .strq .v3 .x7 (16 * (j + 4))]

/-- The slices of the round key at `x0`, to `x7`, and on to the next. -/
def keyBody : List Instr :=
  ([.ldrq .v0 .x0 0, veor .v0 .v0 (B 6), vand .v1 .v0 (B 4), .vop (.shift .ushr .b16 .v0 .v0 4)] : List Instr) ++
  ((List.range 4).flatMap keySlices ++
  ([.vop (.mov (B 6) (B 5)), .addImm .x .x0 .x0 16, .addImm .x .x7 .x7 128, .subImm .x kp kp 1] : List Instr))

/-- The round keys' slices in the scratch buffer. -/
def keys : Prog isa := .seq (.block keySetup) (.loop (.block keyBody) (.nonzero .x kp))

/-! ## Eight blocks -/

/-- A middle round, the round key before its own at `kp`. -/
def roundBody : List Instr :=
  ([.addImm .x kp kp 128] : List Instr) ++ subBytes ++ shiftMix ++ addRoundKey A ++
    ([.subImm .x cnt cnt 1] : List Instr)

def lastRound : List Instr :=
  ([.addImm .x kp kp 128] : List Instr) ++ subBytes ++ permute srOff B ++ addRoundKey B

/-- The eight blocks in `A j` enciphered into `B j`. -/
def encrypt8 : Prog isa :=
  .seq (.block (ortho A ++ ([.addImm .x kp sb 128, .subImm .x cnt .x1 1] : List Instr) ++ addRoundKey A))
    (.seq (.loop (.block roundBody) (.nonzero .x cnt)) (.block (lastRound ++ ortho B)))

/-- A middle round of the inverse cipher, the round key after its own at `kp`. -/
def invRoundBody : List Instr :=
  ([.subImm .x kp kp 128] : List Instr) ++ permute isrOff A ++ invSubBytes ++ addRoundKey B ++ invMix ++
    ([.subImm .x cnt cnt 1] : List Instr)

def invLastRound : List Instr :=
  ([.subImm .x kp kp 128] : List Instr) ++ permute isrOff A ++ invSubBytes ++ addRoundKey B

/-- The eight blocks in `A j` deciphered into `B j`. -/
def decrypt8 : Prog isa :=
  .seq (.block (ortho A ++ ([.lsl .x kp .x1 7, .add .x kp kp sb, .addImm .x kp kp 128,
      .subImm .x cnt .x1 1] : List Instr) ++ addRoundKey A))
    (.seq (.loop (.block invRoundBody) (.nonzero .x cnt)) (.block (invLastRound ++ ortho B)))

/-! ## Groups of blocks -/

/-- Load the blocks `k`, `k + 1`, … at `x3` while there are blocks left
(`x4`), `fuel + 1` at most. -/
def loadFrom : Nat → Nat → Prog isa
  | 0, k => .block [.ldrq (A k) .x3 (16 * k)]
  | fuel + 1, k =>
    .seq (.block [.ldrq (A k) .x3 (16 * k), .subImm .x .x6 .x4 (k + 1)])
      (.ite (.nonzero .x .x6) (loadFrom fuel (k + 1)) (.block []))

/-- Store the results `k`, `k + 1`, … the same way. -/
def storeFrom : Nat → Nat → Prog isa
  | 0, k => .block [.strq (B k) .x3 (16 * k)]
  | fuel + 1, k =>
    .seq (.block [.strq (B k) .x3 (16 * k), .subImm .x .x6 .x4 (k + 1)])
      (.ite (.nonzero .x .x6) (storeFrom fuel (k + 1)) (.block []))

/-- On to the next eight blocks, if more than eight were left. -/
def advance : Prog isa :=
  .seq (.block [.subImm .x .x6 .x4 1, .lsr .x .x6 .x6 3])
    (.ite (.nonzero .x .x6) (.block [.addImm .x .x3 .x3 128, .subImm .x .x4 .x4 8])
      (.block [.movz .x .x4 0 0]))

/-- One group of (up to) eight blocks. -/
def group (crypt8 : Prog isa) : Prog isa :=
  .seq (loadFrom 7 0) (.seq crypt8 (.seq (storeFrom 7 0) advance))

def blocks (crypt8 : Prog isa) : Prog isa :=
  .seq (.block blocksSetup)
    (.ite (.zero .x .x4) (.block [])
      (.seq keys (.loop (group crypt8) (.nonzero .x .x4))))

/-- One to four blocks one at a time by vector permutations (`few`), any
other number bitsliced. -/
def encryptBlocks : Prog isa :=
  .seq (.block isFew) (.ite (.zero .x .x6) (few Vperm.core) (blocks encrypt8))

def decryptBlocks : Prog isa :=
  .seq (.block isFew) (.ite (.zero .x .x6) (few Vperm.Dec.core) (blocks decrypt8))

end VG.Impl.Aes.AArch64.Neon
