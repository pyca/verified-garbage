import VerifiedGarbage.Impl.Aes.Arm.Ctr32
import VerifiedGarbage.Impl.Aes.Arm.Inv

/-!
# AES encryption and decryption of whole blocks, bitsliced, on ARMv7

`vg_aes_encrypt_blocks(schedule = r0, rounds = r1, data = r2, n = r3, scratch = [sp])`
and `vg_aes_decrypt_blocks` with the same arguments (`Spec/Aes/Contract.lean`).

As `vg_aes_ctr32` (`Ctr32.lean`), two blocks at a time, with its round keys
bitsliced in the scratch buffer the same way (the last at byte `lastKey`)
and the callee-saved registers in its slots 32–40. During the key loop the
data pointer waits in `r8`, and `n` in the loop's counter, as
`lr = 16 n + j + 1` before round key `j`: the scratch buffer cannot hold it,
since the analysis of constant time forgets what the buffer holds once the
loop stores to it through a moving pointer. Then each group
of two blocks (or the last one) is loaded from the data into the state
registers as `ortho` takes them, encrypted (`encrypt2`) or decrypted
(`decrypt2`), and stored back in place. Between groups the data left is at
`r10`, the number of blocks left in `r11` and the first round key at
`r12`, stored in slots 45–47 during the transformation.

Decryption runs the inverse cipher (FIPS 197 §5.3) on the round keys of the
forward cipher, from the last down (`Inv.lean`): `kp` starts at the last
round key and steps back 32 bytes each round, and the round loop ends when
it reaches round key 1, 32 bytes after the first round key (in slot
`fkSlot`).

Only the pointers, `rounds`, `n` and what is computed from them (the loop
counters, the round key and data pointers, in registers or stored in the
scratch buffer) are public; no address and no branch depends on anything
else.
-/

namespace VG.Impl.Aes.Arm

open VG.Arm

/-- Load the scratch buffer's base (to `r12`) and save the registers. -/
def blocksPrologue : List Instr := [.ldrSp .r12 0] ++ saveRegs .r12

/-- Set up the key loop as `keySetup` does, with the data pointer (`r2`) to
`r8`, and with `n` in the key loop's counter: `lr := 16 n + rounds + 1`. -/
def blocksKeySetup : List Instr :=
  [.dp .add kp .r12 (.imm (BitVec.ofNat 32 lastKey)), .dp .add .r12 .r0 (.shifted .r1 .lsl 4),
   .mov .lr (.shifted .r3 .lsl 4), .dp .add .lr .lr (.reg .r1), .dp .add .lr .lr (.imm 1),
   movR .r8 .r2]

/-- Step `r12` and `kp` back a round key, and count it in the low 4 bits of `lr`. -/
def blocksKeyStep : List Instr :=
  [.dp .sub .r12 .r12 (.imm 16), .dp .sub kp kp (.imm 32), .dp .sub .lr .lr (.imm 1),
   .dp .and t0 .lr (.imm 15), .cmp t0 (.imm 0)]

/-- Bitslice the round key at `r12` to `kp`, and step back. -/
def blocksKeyBody : List Instr := keyLoad ++ ortho ++ keyStore ++ blocksKeyStep

/-- After the key loop: the first round key to `r12`, the data pointer to
`r10`, the scratch buffer's base to `sb`, the blocks left (`lr = 16 n`) to `r11`. -/
def blocksKeyDone : List Instr :=
  [.dp .add .r12 kp (.imm 32), movR .r10 .r8, .ldrSp sb 0, .mov .r11 (lsrOp .lr 4)]

/-- Load data block `b` (at `r10`): its word `k` into `q (2k + b)`. -/
def loadBlock (b : Nat) : List Instr :=
  (List.range 4).map fun k => .ldr (q (2 * k + b)) .r10 (16 * b + 4 * k)

/-- Store `q (2k + b)` to word `k` of data block `b`. -/
def storeBlock (b : Nat) : List Instr :=
  (List.range 4).map fun k => .str (q (2 * k + b)) .r10 (16 * b + 4 * k)

/-- Two blocks, and on to the next two. -/
def storeFull : List Instr :=
  storeBlock 0 ++ storeBlock 1 ++ [.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)]

/-- The last block (and none left). -/
def storeTail : List Instr := storeBlock 0 ++ [.mov .r11 (.imm 0)]

/-- One group of (up to) two blocks, through `crypt2`. -/
def blockGroup (crypt2 : Prog isa) : Prog isa :=
  .seq (.block (groupSave ++ [.mov .lr (lsrOp .r11 1), .cmp .lr (.imm 0)]))
    (.seq (.ite .ne (.block (loadBlock 0 ++ loadBlock 1)) (.block (loadBlock 0)))
      (.seq crypt2
        (.seq (.block (groupLoad ++ [.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)]))
          (.seq (.ite .ne (.block storeFull) (.block storeTail)) (.block [.cmp .r11 (.imm 0)])))))

/-- The whole function, around `crypt2`. -/
def blocks (crypt2 : Prog isa) : Prog isa :=
  .seq (.block (blocksPrologue ++ blocksKeySetup))
    (.seq (.loop (.block blocksKeyBody) .ne)
      (.seq (.block (blocksKeyDone ++ [.cmp .r11 (.imm 0)]))
        (.seq (.ite .eq (.block []) (.loop (blockGroup crypt2) .ne))
          (.block (.ldrSp .r12 0 :: restoreRegs .r12)))))

/-- A middle round of the inverse cipher, with `kp` at the previous round
key; loops until `kp` is at round key 1. -/
def invRoundBody : List Instr :=
  [.dp .sub kp kp (.imm 32)] ++ invShiftRows ++ invSboxCode ++ addRoundKey ++ invMixColumns ++
  [ldS t0 fkSlot, .dp .sub t0 kp (.reg t0), .cmp t0 (.imm 32)]

/-- The last round of the inverse cipher, with round key 0. -/
def invLastRound : List Instr :=
  [.dp .sub kp kp (.imm 32)] ++ invShiftRows ++ invSboxCode ++ addRoundKey

/-- Decrypt the two blocks in `q 0 … q 7` (as `ortho` takes them), with
the first round key's address in slot `fkSlot`. -/
def decrypt2 : Prog isa :=
  .seq (.block (ortho ++ [.dp .add kp sb (.imm (BitVec.ofNat 32 lastKey))] ++ addRoundKey))
    (.seq (.loop (.block invRoundBody) .ne) (.block (invLastRound ++ ortho)))

def encryptBlocks : Prog isa := blocks encrypt2
def decryptBlocks : Prog isa := blocks decrypt2

end VG.Impl.Aes.Arm
