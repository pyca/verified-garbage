import VerifiedGarbage.Impl.Aes.X86_64.Ctr32
import VerifiedGarbage.Impl.Aes.X86_64.Inv

/-!
# AES encryption and decryption of whole blocks, bitsliced, on x86-64

`vg_aes_encrypt_blocks(schedule = rdi, rounds = rsi, data = rdx, n = rcx, scratch = r8)`
and `vg_aes_decrypt_blocks` with the same arguments (`Spec/Aes/Contract.lean`).

As `vg_aes_ctr32` (`Ctr32.lean`), four blocks at a time, with its round
keys bitsliced in the scratch buffer the same way: after moving the scratch
buffer to `r9` and `n` to `r8`, the callee-saved registers are saved, the
round keys bitsliced (the last at byte `lastKey`), then each group of four
blocks (or the last one to three) is loaded from the data into the state
registers, encrypted (`encrypt4`) or decrypted (`decrypt4`), and stored
back in place.

Decryption runs the inverse cipher (FIPS 197 §5.3) on the round keys of the
forward cipher, from the last down (`Inv.lean`): `kp` starts at the last
round key and steps back 64 bytes each round, and the round loop ends when
it reaches round key 1, at `rdi + 64`.

Only `rdi` (the first round key), `rsi`, `rdx` (the data), `r8` (the blocks
left), `r9` and `r15` during the key loop hold public values; no address
and no branch depends on anything else.
-/

namespace VG.Impl.Aes.X86_64

open VG.X86_64

/-- The scratch buffer to `r9`, the number of blocks to `r8` (the data stays
in `rdx`). -/
def blocksSetup : List Instr := [movR .r9 .r8, movR .r8 .rcx]

/-- Load data block `b`: bytes 0–7 into `q b`, bytes 8–15 into `q (b + 4)`. -/
def loadBlock (b : Nat) : List Instr :=
  [.mov (q b) (.mem (at_ .rdx (16 * b))), .mov (q (b + 4)) (.mem (at_ .rdx (16 * b + 8)))]

/-- Store `q b` and `q (b + 4)` to data block `b`. -/
def storeBlock (b : Nat) : List Instr :=
  [.store (at_ .rdx (16 * b)) (q b), .store (at_ .rdx (16 * b + 8)) (q (b + 4))]

/-- Four blocks. -/
def loadFull : List Instr := (List.range 4).flatMap loadBlock

/-- The last one to three blocks. -/
def loadTail : Prog isa :=
  .seq (.block (loadBlock 0 ++ [.alu .cmp .r8 (.imm 2)]))
    (.ite .ae (.seq (.block (loadBlock 1 ++ [.alu .cmp .r8 (.imm 3)]))
        (.ite .ae (.block (loadBlock 2)) (.block [])))
      (.block []))

/-- Four blocks, and on to the next four (ZF is set when none are left). -/
def storeFull : List Instr :=
  (List.range 4).flatMap storeBlock ++ [.alu .add .rdx (.imm 64), .alu .sub .r8 (.imm 4)]

/-- The last one to three blocks (and ZF set). -/
def storeTail : Prog isa :=
  .seq (.block (storeBlock 0 ++ [.alu .cmp .r8 (.imm 2)]))
    (.seq (.ite .ae (.seq (.block (storeBlock 1 ++ [.alu .cmp .r8 (.imm 3)]))
        (.ite .ae (.block (storeBlock 2)) (.block [])))
      (.block []))
    (.block [.alu .sub .r8 (.reg .r8)]))

/-- One group of (up to) four blocks, through `crypt4`. -/
def blockGroup (crypt4 : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 4)])
    (.seq (.ite .ae (.block loadFull) loadTail)
      (.seq crypt4
        (.seq (.block [.alu .cmp .r8 (.imm 4)]) (.ite .ae (.block storeFull) storeTail))))

/-- The whole function, around `crypt4`. -/
def blocks (crypt4 : Prog isa) : Prog isa :=
  .seq (.block (blocksSetup ++ saveRegs ++ keySetup))
    (.seq (.loop (.block keyBody) .ae)
      (.seq (.block (keyDone ++ [.alu .test .r8 (.reg .r8)]))
        (.seq (.ite .e (.block []) (.loop (blockGroup crypt4) .ne)) (.block restoreRegs))))

/-- A middle round of the inverse cipher, with `kp` at the previous round
key; loops until `kp` is at round key 1. -/
def invRoundBody : List Instr :=
  [.alu .sub kp (.imm 64)] ++ invShiftRows ++ invSboxCode ++ addRoundKey ++ invMixColumns ++
  [movR t0 .rdi, .alu .add t0 (.imm 64), .alu .cmp kp (.reg t0)]

/-- The last round of the inverse cipher, with round key 0. -/
def invLastRound : List Instr :=
  [.alu .sub kp (.imm 64)] ++ invShiftRows ++ invSboxCode ++ addRoundKey

/-- Decrypt the four blocks in `q 0 … q 7` (as `toBs` takes them). -/
def decrypt4 : Prog isa :=
  .seq (.block (toBs ++ [movR kp sb, .alu .add kp (.imm (BitVec.ofNat 32 lastKey))] ++ addRoundKey))
    (.seq (.loop (.block invRoundBody) .ne) (.block (invLastRound ++ fromBs)))

def encryptBlocks : Prog isa := blocks encrypt4
def decryptBlocks : Prog isa := blocks decrypt4

end VG.Impl.Aes.X86_64
