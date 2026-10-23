module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Impl.Aes.PPC64LE.Inv

/-!
# AES encryption and decryption of whole blocks, bitsliced, on PPC64LE

`vg_aes_encrypt_blocks(schedule = r3, rounds = r4, data = r5, n = r6, scratch = r7)`
and `vg_aes_decrypt_blocks` with the same arguments (`Spec/Aes/Contract.lean`).

As `vg_aes_ctr32` (`Ctr32.lean`), four blocks at a time, with its round
keys bitsliced in the scratch buffer the same way: after moving the scratch
buffer to `r8`, `n` to `r7` and the data to `r6`, the nonvolatile registers
are saved, the round keys bitsliced (the last at byte `lastKey`), then each
group of four blocks (or the last one to three) is loaded from the data into
the state registers, encrypted (`encrypt4`) or decrypted (`decrypt4`), and
stored back in place.

Decryption runs the inverse cipher (FIPS 197 §5.3) on the round keys of the
forward cipher, from the last down (`Inv.lean`): `kp` starts at the last
round key and steps back 64 bytes each round, and the round loop ends when
it reaches round key 1, at `r3 + 64`.

Only `r3` (the first round key), `r4`, `r5`, `r6` (the data), `r7` (the
blocks left), `r8` and what is computed from them in `t0` for the branches
hold public values; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE

open VG.PPC64LE

/-- The scratch buffer to `r8`, the number of blocks to `r7`, the data to `r6`. -/
def blocksSetup : List Instr := [movR .r8 .r7, movR .r7 .r6, movR .r6 .r5]

/-- Load data block `b`: bytes 0–7 into `q b`, bytes 8–15 into `q (b + 4)`. -/
def loadBlock (b : Nat) : List Instr :=
  [.load .d (q b) .r6 (16 * b), .load .d (q (b + 4)) .r6 (16 * b + 8)]

/-- Store `q b` and `q (b + 4)` to data block `b`. -/
def storeBlock (b : Nat) : List Instr :=
  [.store .d (q b) .r6 (16 * b), .store .d (q (b + 4)) .r6 (16 * b + 8)]

/-- Four blocks. -/
def loadFull : List Instr := (List.range 4).flatMap loadBlock

/-- The last one to three blocks. -/
def loadTail : Prog isa :=
  .seq (.block (loadBlock 0 ++ ([.subi t0 .r7 1] : List Instr)))
    (.ite (.nonzero .d t0) (.seq (.block (loadBlock 1 ++ ([.subi t0 .r7 3] : List Instr)))
        (.ite (.zero .d t0) (.block (loadBlock 2)) (.block [])))
      (.block []))

/-- Four blocks, and on to the next four. -/
def storeFull : List Instr :=
  (List.range 4).flatMap storeBlock ++ ([.addi .r6 .r6 64, .subi .r7 .r7 4] : List Instr)

/-- The last one to three blocks (and none left). -/
def storeTail : Prog isa :=
  .seq (.block (storeBlock 0 ++ ([.subi t0 .r7 1] : List Instr)))
    (.seq (.ite (.nonzero .d t0) (.seq (.block (storeBlock 1 ++ ([.subi t0 .r7 3] : List Instr)))
        (.ite (.zero .d t0) (.block (storeBlock 2)) (.block [])))
      (.block []))
    (.block [.li .r7 0]))

/-- One group of (up to) four blocks, through `crypt4`. -/
def blockGroup (crypt4 : Prog isa) : Prog isa :=
  .seq (.block [shrI t0 .r7 2])
    (.seq (.ite (.nonzero .d t0) (.block loadFull) loadTail)
      (.seq crypt4
        (.seq (.block [shrI t0 .r7 2]) (.ite (.nonzero .d t0) (.block storeFull) storeTail))))

/-- The whole function, around `crypt4`. -/
def blocks (crypt4 : Prog isa) : Prog isa :=
  .seq (.block (blocksSetup ++ saveRegs ++ keySetup))
    (.seq (.loop (.block keyBody) (.nonzero .d .r4))
      (.seq (.block keyDone)
        (.seq (.ite (.zero .d .r7) (.block []) (.loop (blockGroup crypt4) (.nonzero .d .r7)))
          (.block restoreRegs))))

/-- A middle round of the inverse cipher, with `kp` at the previous round
key; loops until `kp` is at round key 1. -/
def invRoundBody : List Instr :=
  ([.subi kp kp 64] : List Instr) ++ invShiftRows ++ invSboxCode ++ addRoundKey ++ invMixColumns ++
  [.sub t0 kp .r3, .subi t0 t0 64]

/-- The last round of the inverse cipher, with round key 0. -/
def invLastRound : List Instr :=
  ([.subi kp kp 64] : List Instr) ++ invShiftRows ++ invSboxCode ++ addRoundKey

/-- Decrypt the four blocks in `q 0 … q 7` (as `toBs` takes them). -/
def decrypt4 : Prog isa :=
  .seq (.block (toBs ++ [.addi kp sb lastKey] ++ addRoundKey))
    (.seq (.loop (.block invRoundBody) (.nonzero .d t0)) (.block (invLastRound ++ fromBs)))

def encryptBlocks : Prog isa := blocks encrypt4
def decryptBlocks : Prog isa := blocks decrypt4

end VG.Impl.Aes.PPC64LE
