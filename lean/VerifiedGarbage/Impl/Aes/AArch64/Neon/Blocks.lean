module

public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Sbox
public import VerifiedGarbage.Impl.Aes.AArch64.Blocks

/-!
# AES encryption and decryption of whole blocks, bitsliced in AdvSIMD registers, on AArch64

`vg_aes_encrypt_blocks_neon(schedule = x0, rounds = x1, data = x2, n = x3, scratch = x4)`
and `vg_aes_decrypt_blocks_neon` with the same arguments, as
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (`Blocks.lean`): eight
blocks at a time, bitsliced in eight 128-bit registers.

* The state of eight blocks is eight words, word `j` holding bit `j` of the
  128 bytes: bit `b` of its byte `i` is bit `j` of byte `i` of block `b`,
  the bytes as FIPS 197 lays them out (byte `r + 4c` is row `r` of column
  `c`). `ortho` (BearSSL's `br_aes_ct64_ortho`, Thomas Pornin, MIT licence,
  on each doubleword) takes the eight blocks, one in each register, to
  that, and back.
* SubBytes is the circuit of `Sbox.lean`, from the registers `A j` to
  `B j`. ShiftRows permutes the bytes of each word, one `tbl` by a constant;
  MixColumns rotates the columns, which are the 32-bit lanes, by one byte
  (`tbl`) and by two (`rev32` of the halfwords): with `rⱼ` the word `j`
  rotated by one byte and `uⱼ = qⱼ ⊕ rⱼ`, the result's word `j` is
  `uⱼ₋₁ ⊕ [j ∈ {1, 3, 4}] u₇ ⊕ rⱼ ⊕ (uⱼ rotated by two bytes)`, with `u₇`
  for `u₋₁`, as in BearSSL's `mix_columns`. AddRoundKey XORs the bitsliced
  round key at `kp`.
* The round keys are bitsliced once a call, into the scratch buffer from
  byte 128 on, 128 bytes each: bit `j` of a byte of the round key is every
  bit of that byte of word `j` (`cmeq` of the byte masked by `2ʲ`, with
  `2ʲ`). The first 96 bytes of the scratch buffer are the S-boxes' slots.
* Each group of eight blocks, or the last one to seven: its blocks are
  loaded (`loadFrom`), encrypted or decrypted, and stored back
  (`storeFrom`); the words of the blocks that are not there hold whatever
  the registers did, and are not stored.
* Decryption runs the inverse cipher (FIPS 197 §5.3) from the last round
  key down: InvShiftRows, the inverse S-box, AddRoundKey, and InvMixColumns
  as MixColumns after `invMcPre` (`Inv.lean`).

Only `x0`, `x3`–`x9`, `v0`–`v7` and `v16`–`v31` are written. `x0`, `x1`,
`x3`, `x4`, `x5`, `x7`, `kp` and `cnt` hold public values, and no address or
branch depends on anything else.

`vg_aes_encrypt_blocks_neon` is `encryptBlocks`: one block (`n = 1`) is
encrypted by table lookups (`OneBlock.lean`), as `vg_aes_encrypt_blocks`
does it, with nothing bitsliced.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Neon

open VG.AArch64
open VG.Impl.Tbl.AArch64 (const64 const128)

/-- A temporary. -/
def tmp : VReg := .v24

/-- The indices of a `tbl`. -/
def idxR : VReg := .v25

/-- The register pointing to the bitsliced round key. -/
def kp : Reg := .x8

/-- The rounds, or round keys, left. -/
def cnt : Reg := .x9

/-! ## Between bytes and the bitsliced state -/

/-- The registers of the masks of `ortho`. -/
def mreg : Nat → VReg
  | 0 => .v29 | 1 => .v30 | _ => .v31

/-- The masks of `ortho`, in each doubleword. -/
def orthoMasks : List (Nat × BitVec 64) :=
  [(0, 0x5555555555555555), (1, 0x3333333333333333), (2, 0x0F0F0F0F0F0F0F0F)]

def setMasks : List Instr :=
  orthoMasks.flatMap fun (k, v) => const64 .x6 v ++ [.vop (.dup .d2 (mreg k) .x6)]

/-- A delta swap between `x` and `y` (BearSSL's `SWAPN`): exchanges the bits
of `y` in the mask `mreg k` with the bits of `x` `s` places above them. -/
def swapBetween (x y : VReg) (k s : Nat) : List Instr :=
  [.vop (.shift .ushr .d2 tmp x s), veor tmp tmp y, vand tmp tmp (mreg k), veor y y tmp,
   .vop (.shift .shl .d2 tmp tmp s), veor x x tmp]

/-- BearSSL's `br_aes_ct64_ortho` on the words `P 0 … P 7`: transposes the
8×8 bit matrix in each byte position of the eight words. -/
def ortho (P : Nat → VReg) : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapBetween (P a) (P b) 0 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapBetween (P a) (P b) 1 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapBetween (P a) (P b) 2 4)

/-- `ortho` of the words `P 0 … P 7`, with its masks. -/
def bitslice (P : Nat → VReg) : List Instr := setMasks ++ ortho P

/-! ## The round transformations -/

/-- ShiftRows as the indices of a `tbl`: byte `t` of the result is byte
`t mod 4 + 4 ((t / 4 + t mod 4) mod 4)`. -/
def srIdx : BitVec 128 := ofVBytes fun t => BitVec.ofNat 8 (t % 4 + 4 * ((t / 4 + t % 4) % 4))

/-- InvShiftRows: byte `t` of the result is byte `t mod 4 + 4 ((t / 4 + 4 - t mod 4) mod 4)`. -/
def invSrIdx : BitVec 128 :=
  ofVBytes fun t => BitVec.ofNat 8 (t % 4 + 4 * ((t / 4 + 4 - t % 4) % 4))

/-- The next row of each column: byte `t` of the result is byte `4 ⌊t / 4⌋ + (t + 1) mod 4`. -/
def rotIdx : BitVec 128 := ofVBytes fun t => BitVec.ofNat 8 (4 * (t / 4) + (t + 1) % 4)

/-- A `tbl` of each of the words `P 0 … P 7`, in place, by the indices in `idxR`. -/
def tbls (P : Nat → VReg) : List Instr := (List.range 8).map fun j => .vop (.tbl (P j) (P j) idxR)

/-- The bytes of each of the words `P 0 … P 7` permuted by the indices `c`. -/
def permBytes (P : Nat → VReg) (c : BitVec 128) : List Instr := const128 idxR c ++ tbls P

/-- Output word `j` of MixColumns, in `A j`, which holds `rⱼ`; `B k` holds `uₖ`. -/
def mcOut (j : Nat) : List Instr :=
  [veor (A j) (A j) (B ((j + 7) % 8))] ++
  (if j = 1 ∨ j = 3 ∨ j = 4 then [veor (A j) (A j) (B 7)] else []) ++
  [.vop (.rev .rev32h tmp (B j)), veor (A j) (A j) tmp]

/-- MixColumns, from the state in `B 0 … B 7` to `A 0 … A 7`, with `rotIdx` in `idxR`. -/
def mcCore : List Instr :=
  ((List.range 8).flatMap fun j => [.vop (.tbl (A j) (B j) idxR), veor (B j) (B j) (A j)]) ++
  (List.range 8).flatMap mcOut

/-- MixColumns: from the state in `B 0 … B 7` to `A 0 … A 7`. -/
def mixColumns : List Instr := const128 idxR rotIdx ++ mcCore

/-- Each column times `{04}x² + {05}` (`Inv.lean`'s `invMcPre`), in place in
`B 0 … B 7`: with `uⱼ = qⱼ ⊕ (qⱼ rotated by two bytes)` in `A j`,
`qⱼ ⊕= ({04} • u)ⱼ`. -/
def invMcPre : List Instr :=
  ((List.range 8).flatMap fun j => [.vop (.rev .rev32h (A j) (B j)), veor (A j) (A j) (B j)]) ++
  ((List.range 8).flatMap fun j => (times4 j).map fun k => veor (B j) (B j) (A k))

/-- InvMixColumns, from the state in `B 0 … B 7` to `A 0 … A 7`: MixColumns after `invMcPre`. -/
def invMixColumns : List Instr := const128 idxR rotIdx ++ (invMcPre ++ mcCore)

/-- AddRoundKey of the words `P 0 … P 7`, with the bitsliced round key at `kp`. -/
def addRoundKey (P : Nat → VReg) : List Instr :=
  (List.range 8).flatMap fun j => [.ldrq tmp kp (16 * j), veor (P j) (P j) tmp]

/-! ## Eight blocks -/

/-- A middle round, with `kp` at the previous round key. -/
def roundBody : List Instr :=
  ([.addImm .x kp kp 128] : List Instr) ++ sboxCode ++ permBytes B srIdx ++ mixColumns ++
  addRoundKey A ++ ([.subImm .x cnt cnt 1] : List Instr)

/-- The last round. -/
def lastRound : List Instr :=
  ([.addImm .x kp kp 128] : List Instr) ++ sboxCode ++ permBytes B srIdx ++ addRoundKey B

/-- Encrypt the eight blocks in `A 0 … A 7`, into `B 0 … B 7`. -/
def encrypt8 : Prog isa :=
  .seq (.block (bitslice A ++ ([.addImm .x kp sb 128, .subImm .x cnt .x1 1] : List Instr) ++
      addRoundKey A))
    (.seq (.loop (.block roundBody) (.nonzero .x cnt)) (.block (lastRound ++ bitslice B)))

/-- A middle round of the inverse cipher, with `kp` at the next round key. -/
def invRoundBody : List Instr :=
  ([.subImm .x kp kp 128] : List Instr) ++ permBytes A invSrIdx ++ invSboxCode ++ addRoundKey B ++
  invMixColumns ++ ([.subImm .x cnt cnt 1] : List Instr)

/-- The last round of the inverse cipher, with round key 0. -/
def invLastRound : List Instr :=
  ([.subImm .x kp kp 128] : List Instr) ++ permBytes A invSrIdx ++ invSboxCode ++ addRoundKey B

/-- Decrypt the eight blocks in `A 0 … A 7`, into `B 0 … B 7`. -/
def decrypt8 : Prog isa :=
  .seq (.block (bitslice A ++
      ([.lsl .x kp .x1 7, .add .x kp kp sb, .addImm .x kp kp 128, .subImm .x cnt .x1 1] : List Instr) ++
      addRoundKey A))
    (.seq (.loop (.block invRoundBody) (.nonzero .x cnt)) (.block (invLastRound ++ bitslice B)))

/-! ## The round keys -/

/-- `2ʲ` in every byte of `B j`. -/
def keyMask (j : Nat) : List Instr :=
  [.movz .w .x6 (BitVec.ofNat 16 (2 ^ j)) 0, .vop (.dup .b16 (B j) .x6)]

def keyMasks : List Instr := (List.range 8).flatMap keyMask

/-- The masks, `x7 := ` where the first bitsliced round key goes, and
`kp := rounds + 1`, the round keys left. -/
def keySetup : List Instr :=
  keyMasks ++ ([.addImm .x .x7 sb 128, .addImm .x kp .x1 1] : List Instr)

/-- Word `j` of the round key in `v0`, to `[x7, #16j]`. -/
def sliceWord (j : Nat) : List Instr :=
  [vand .v1 .v0 (B j), .vop (.cmeq .b16 .v1 .v1 (B j)), .strq .v1 .x7 (16 * j)]

/-- Bitslice the round key at `x0` to `x7`, and step both on. -/
def keyBody : List Instr :=
  ([.ldrq .v0 .x0 0] : List Instr) ++ (List.range 8).flatMap sliceWord ++
  ([.addImm .x .x0 .x0 16, .addImm .x .x7 .x7 128, .subImm .x kp kp 1] : List Instr)

/-! ## The blocks -/

/-- Load data blocks `k`, `k + 1`, … while there are blocks left (`x4`),
`fuel + 1` at most, into `A k`, …. -/
def loadFrom : Nat → Nat → Prog isa
  | 0, k => .block [.ldrq (A k) .x3 (16 * k)]
  | fuel + 1, k =>
    .seq (.block [.ldrq (A k) .x3 (16 * k), .subImm .x .x6 .x4 (k + 1)])
      (.ite (.nonzero .x .x6) (loadFrom fuel (k + 1)) (.block []))

/-- Store `B k`, … to the data blocks `k`, `k + 1`, … while there are blocks left. -/
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

/-- One group of (up to) eight blocks, through `crypt8`. -/
def group (crypt8 : Prog isa) : Prog isa :=
  .seq (loadFrom 7 0) (.seq crypt8 (.seq (storeFrom 7 0) advance))

/-- The whole function, around `crypt8`: after `blocksSetup` (the scratch
buffer to `x5`, the number of blocks to `x4`, the data to `x3`). -/
def blocks (crypt8 : Prog isa) : Prog isa :=
  .seq (.block blocksSetup)
    (.ite (.zero .x .x4) (.block [])
      (.seq (.block keySetup)
        (.seq (.loop (.block keyBody) (.nonzero .x kp)) (.loop (group crypt8) (.nonzero .x .x4)))))

/-- `vg_aes_encrypt_blocks_neon`: one block by table lookups, any other
number of blocks bitsliced. -/
def encryptBlocks : Prog isa :=
  .seq (.block [.subImm .x .x6 .x3 1]) (.ite (.zero .x .x6) encryptOne (blocks encrypt8))

/-- `vg_aes_decrypt_blocks_neon`. -/
def decryptBlocks : Prog isa := blocks decrypt8

end VG.Impl.Aes.AArch64.Neon
