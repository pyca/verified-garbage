module

public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32

/-!
# AES encryption and decryption of whole blocks, bitsliced, on RISC-V

`vg_aes_encrypt_blocks(schedule = a0, rounds = a1, data = a2, n = a3, scratch = a4)`
and `vg_aes_decrypt_blocks` with the same arguments (`Spec/Aes/Contract.lean`).

As `vg_aes_ctr32` (`Ctr32.lean`), four blocks at a time, with its round
keys bitsliced in the scratch buffer the same way: after moving the scratch
buffer to `a5` (rounded up to a multiple of 8), `n` to `a4` and the data to
`a3`, the callee-saved registers are saved, the masks built, the round keys
bitsliced (the last at byte `lastKey`), then each group of four blocks (or
the last one to three) is loaded from the data into the state registers, a
byte at a time, encrypted (`encrypt4`) or decrypted (`decrypt4`), and stored
back in place.

Decryption runs the inverse cipher (FIPS 197 §5.3) on the round keys of the
forward cipher, from the last down (`Inv.lean`): `kp` starts at the last
round key and steps back 64 bytes each round, and the round loop ends when
it reaches round key 1, at `a0 + 64`.

Only `a0` (the first round key), `a1`, `a2`, `a3` (the data), `a4` (the
blocks left), `a5` and what is computed from them in `t0` for the branches
hold public values; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

/-- The scratch buffer to `a5`, the number of blocks to `a4`, the data to `a3`. -/
def blocksSetup : List Instr := [movR sb .a4, movR .a4 .a3, movR .a3 .a2]

/-- Load data block `b`: bytes 0–7 into `q b`, bytes 8–15 into `q (b + 4)`, by
doublewords if `w` (the data aligned), else a byte at a time. -/
def loadBlock (w : Bool) (b : Nat) : List Instr :=
  loadLE64W w (q b) t0 t1 .a3 (16 * b) ++ loadLE64W w (q (b + 4)) t0 t1 .a3 (16 * b + 8)

/-- Store `q b` and `q (b + 4)` to data block `b`. -/
def storeBlock (w : Bool) (b : Nat) : List Instr :=
  storeLE64W w (q b) t0 t1 .a3 (16 * b) ++ storeLE64W w (q (b + 4)) t0 t1 .a3 (16 * b + 8)

/-- Four blocks. -/
def loadFull (w : Bool) : List Instr := (List.range 4).flatMap (loadBlock w)

/-- The last one to three blocks. -/
def loadTail (w : Bool) : Prog isa :=
  .seq (.block (loadBlock w 0 ++ ([.addi t0 .a4 (-1)] : List Instr)))
    (.ite (.nonzero t0) (.seq (.block (loadBlock w 1 ++ ([.addi t0 .a4 (-3)] : List Instr)))
        (.ite (.zero t0) (.block (loadBlock w 2)) (.block [])))
      (.block []))

/-- Four blocks, and on to the next four. -/
def storeFull (w : Bool) : List Instr :=
  (List.range 4).flatMap (storeBlock w) ++ ([.addi .a3 .a3 64, .addi .a4 .a4 (-4)] : List Instr)

/-- The last one to three blocks (and none left). -/
def storeTail (w : Bool) : Prog isa :=
  .seq (.block (storeBlock w 0 ++ ([.addi t0 .a4 (-1)] : List Instr)))
    (.seq (.ite (.nonzero t0) (.seq (.block (storeBlock w 1 ++ ([.addi t0 .a4 (-3)] : List Instr)))
        (.ite (.zero t0) (.block (storeBlock w 2)) (.block [])))
      (.block []))
    (.block [.li .a4 0]))

/-- One group of (up to) four blocks, through `crypt4`, by doublewords if `w`. -/
def blockGroup (w : Bool) (crypt4 : Prog isa) : Prog isa :=
  .seq (.block [shrI t0 .a4 2])
    (.seq (.ite (.nonzero t0) (.block (loadFull w)) (loadTail w))
      (.seq crypt4
        (.seq (.block [shrI t0 .a4 2]) (.ite (.nonzero t0) (.block (storeFull w)) (storeTail w)))))

/-- The groups: by doublewords if the data's address is a multiple of 8
(`t0 = a3 ∧ 7`, of a public address), else a byte at a time. -/
def groups (crypt4 : Prog isa) : Prog isa :=
  .seq (.block [.logicImm .and t0 .a3 7])
    (.ite (.zero t0) (.loop (blockGroup true crypt4) (.nonzero .a4)) (.loop (blockGroup false crypt4) (.nonzero .a4)))

/-- The whole function, around `crypt4`. -/
def blocks (crypt4 : Prog isa) : Prog isa :=
  .seq (.block (blocksSetup ++ roundSb ++ saveRegs ++ maskInit ++ keySetup))
    (.seq (.loop (.block keyBody) (.nonzero .a1))
      (.seq (.block keyDone)
        (.seq (.ite (.zero .a4) (.block []) (groups crypt4))
          (.block restoreRegs))))

/-- A middle round of the inverse cipher, with `kp` at the previous round
key; loops until `kp` is at round key 1. -/
def invRoundBody : List Instr :=
  ([.addi kp kp (-64)] : List Instr) ++ invShiftRows ++ invSboxCode ++ addRoundKey ++
  invMixColumns ++ [.sub t0 kp .a0, .addi t0 t0 (-64)]

/-- The last round of the inverse cipher, with round key 0. -/
def invLastRound : List Instr :=
  ([.addi kp kp (-64)] : List Instr) ++ invShiftRows ++ invSboxCode ++ addRoundKey

/-- Decrypt the four blocks in `q 0 … q 7` (as `toBs` takes them). -/
def decrypt4 : Prog isa :=
  .seq (.block (toBs ++ [.addi kp sb lastKey] ++ addRoundKey))
    (.seq (.loop (.block invRoundBody) (.nonzero t0)) (.block (invLastRound ++ fromBs)))

def encryptBlocks : Prog isa := blocks encrypt4
def decryptBlocks : Prog isa := blocks decrypt4

end VG.Impl.Aes.RISCV64
