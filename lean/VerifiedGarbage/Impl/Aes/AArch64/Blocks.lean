module

public import VerifiedGarbage.Impl.Aes.AArch64.Ctr32
public import VerifiedGarbage.Impl.Aes.AArch64.Inv
public import VerifiedGarbage.Impl.Aes.AArch64.Vperm

/-!
# AES encryption and decryption of whole blocks, bitsliced, on AArch64

`vg_aes_encrypt_blocks(schedule = x0, rounds = x1, data = x2, n = x3, scratch = x4)`
and `vg_aes_decrypt_blocks` with the same arguments (`Spec/Aes/Contract.lean`).

As `vg_aes_ctr32` (`Ctr32.lean`), four blocks at a time, with its round
keys bitsliced in the scratch buffer the same way: after moving the scratch
buffer to `x5`, `n` to `x4` and the data to `x3` (where `vg_aes_ctr32` has
them), the callee-saved registers are saved, the round keys bitsliced (the
last at byte `lastKey`), then each group of four blocks (or the last one to
three) is loaded from the data into the state registers, encrypted
(`encrypt4`) or decrypted (`decrypt4`), and stored back in place.

Decryption runs the inverse cipher (FIPS 197 §5.3) on the round keys of the
forward cipher, from the last down (`Inv.lean`): `kp` starts at the last
round key and steps back 64 bytes each round, and the round loop ends when
it reaches round key 1, at `x0 + 64`.

Only `x0` (the first round key), `x1`, `x2` during the key loop, `x3` (the
data), `x4` (the blocks left), `x5` and the loop tests (`t0`) hold public
values; no address and no branch depends on anything else.

`vg_aes_encrypt_blocks` is `encryptBlocksN`, and `vg_aes_decrypt_blocks` is
`decryptBlocksN`: they do not run the bitsliced code above, but take every
block one at a time by vector permutations (`Vperm.lean`, `few`), with no
round key bitsliced and nothing written to `scratch`, which costs less at
every size (measured).
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- The scratch buffer to `x5`, the number of blocks to `x4`, the data to `x3`. -/
def blocksSetup : List Instr := [movR .x5 .x4, movR .x4 .x3, movR .x3 .x2]

/-- Load data block `b`: bytes 0–7 into `q b`, bytes 8–15 into `q (b + 4)`. -/
def loadBlock (b : Nat) : List Instr :=
  [.ldr .x (q b) .x3 (16 * b), .ldr .x (q (b + 4)) .x3 (16 * b + 8)]

/-- Store `q b` and `q (b + 4)` to data block `b`. -/
def storeBlock (b : Nat) : List Instr :=
  [.str .x (q b) .x3 (16 * b), .str .x (q (b + 4)) .x3 (16 * b + 8)]

/-- Four blocks. -/
def loadFull : List Instr := (List.range 4).flatMap loadBlock

/-- The last one to three blocks. -/
def loadTail : Prog isa :=
  .seq (.block (loadBlock 0 ++ ([.subImm .x t0 .x4 1] : List Instr)))
    (.ite (.nonzero .x t0) (.seq (.block (loadBlock 1 ++ ([.subImm .x t0 .x4 2] : List Instr)))
        (.ite (.nonzero .x t0) (.block (loadBlock 2)) (.block [])))
      (.block []))

/-- Four blocks, and on to the next four. -/
def storeFull : List Instr :=
  (List.range 4).flatMap storeBlock ++ ([.addImm .x .x3 .x3 64, .subImm .x .x4 .x4 4] : List Instr)

/-- The last one to three blocks (and none left). -/
def storeTail : Prog isa :=
  .seq (.block (storeBlock 0 ++ ([.subImm .x t0 .x4 1] : List Instr)))
    (.seq (.ite (.nonzero .x t0) (.seq (.block (storeBlock 1 ++ ([.subImm .x t0 .x4 2] : List Instr)))
        (.ite (.nonzero .x t0) (.block (storeBlock 2)) (.block [])))
      (.block []))
    (.block [.movz .x .x4 0 0]))

/-- One group of (up to) four blocks, through `crypt4`. -/
def blockGroup (crypt4 : Prog isa) : Prog isa :=
  .seq (.block [lsrI t0 .x4 2])
    (.seq (.ite (.nonzero .x t0) (.block loadFull) loadTail)
      (.seq crypt4
        (.seq (.block [lsrI t0 .x4 2]) (.ite (.nonzero .x t0) (.block storeFull) storeTail))))

/-- The whole function, around `crypt4`. -/
def blocks (crypt4 : Prog isa) : Prog isa :=
  .seq (.block (blocksSetup ++ saveRegs ++ keySetup))
    (.seq (.loop (.block keyBody) (.nonzero .x .x2))
      (.seq (.block keyDone)
        (.seq (.ite (.zero .x .x4) (.block []) (.loop (blockGroup crypt4) (.nonzero .x .x4)))
          (.block restoreRegs))))

/-- A middle round of the inverse cipher, with `kp` at the previous round
key; loops until `kp` is at round key 1 (`t0 = 0`). -/
def invRoundBody : List Instr :=
  ([.subImm .x kp kp 64] : List Instr) ++ invShiftRows ++ invSboxCode ++ addRoundKey ++ invMixColumns ++
  ([.sub .x t0 kp .x0, .subImm .x t0 t0 64] : List Instr)

/-- The last round of the inverse cipher, with round key 0. -/
def invLastRound : List Instr :=
  ([.subImm .x kp kp 64] : List Instr) ++ invShiftRows ++ invSboxCode ++ addRoundKey

/-- Decrypt the four blocks in `q 0 … q 7` (as `toBs` takes them). -/
def decrypt4 : Prog isa :=
  .seq (.block (toBs ++ ([.addImm .x kp sb lastKey] : List Instr) ++ addRoundKey))
    (.seq (.loop (.block invRoundBody) (.nonzero .x t0)) (.block (invLastRound ++ fromBs)))

def encryptBlocks : Prog isa := blocks encrypt4
def decryptBlocks : Prog isa := blocks decrypt4

/-- One block of `few`: the block at `x2` through `core` in place, on to
the next, and `x0` and `x1`, which `core` writes, back from `x9` and
`x10`. -/
def fewBody (core : Prog isa) : Prog isa :=
  .seq (.block [.ldrq .v0 .x2 0])
    (.seq core (.block [.strq .v0 .x2 0, .addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1,
      movR .x0 .x9, movR .x1 .x10]))

/-- The `x3` blocks at `x2` (one at least), each through `core` (`v0 :=
core(v0)`, the schedule at `x0`, the rounds in `x1`) in place: a few blocks
one at a time, which costs less than a bitsliced batch. -/
def few (core : Prog isa) : Prog isa :=
  .seq (.block [movR .x9 .x0, movR .x10 .x1]) (.loop (fewBody core) (.nonzero .x .x3))

/-- `x6 := 0` for one to four blocks (`x3`), which go one at a time: a batch
costs more than five blocks do (measured). -/
def isFew : List Instr := [.subImm .x .x6 .x3 1, .lsr .x .x6 .x6 2]

/-- `vg_aes_encrypt_blocks`: nothing for no block, else each block by
vector permutations, one at a time. -/
def encryptBlocksN : Prog isa :=
  .ite (.zero .x .x3) (.block []) (few Vperm.core)

/-- `vg_aes_decrypt_blocks`: nothing for no block, else each block by
vector permutations, one at a time. -/
def decryptBlocksN : Prog isa :=
  .ite (.zero .x .x3) (.block []) (few Vperm.Dec.core)

end VG.Impl.Aes.AArch64
