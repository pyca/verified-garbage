import VerifiedGarbage.Impl.Aes.X86.Ctr32
import VerifiedGarbage.Impl.Aes.X86.Inv

/-!
# AES encryption and decryption of whole blocks, bitsliced, on x86 (32-bit)

`vg_aes_encrypt_blocks(schedule, rounds, data, n, scratch)` and
`vg_aes_decrypt_blocks` with the same arguments (`Spec/Aes/Contract.lean`),
cdecl: the arguments are at `[esp + 4]` … `[esp + 20]`.

As `vg_aes_ctr32` (`Ctr32.lean`), two blocks at a time, with its round keys
bitsliced in the scratch buffer the same way, and the callee-saved
registers, the data pointer and the number of blocks left kept there too:
after the round keys are bitsliced, each group of two blocks (or the last
one, loaded into both halves of the state) is loaded from the data into
slots `0 … 7`, encrypted (`encrypt2`) or decrypted (`decrypt2`), and
stored back in place.

Decryption runs the inverse cipher (FIPS 197 §5.3) on the round keys of the
forward cipher, from the last down (`Inv.lean`): `kp` starts at the last
round key and steps back 32 bytes each round, and the round loop ends when
it reaches round key 1, at `edi + lastKey + 32 - 32 rounds`.

Every address is `esp` or a pointer plus a constant, or computed from the
pointers and `rounds`, and every branch depends only on those and `n`, so
only the pointers, `rounds` and `n` can affect timing.
-/

namespace VG.Impl.Aes.X86

open VG.X86

/-- Store the data pointer and the count, and test the count. -/
def blocksSetup : List Instr :=
  [.mov .eax (.mem (argOp 2)), .store (at_ .edi dOff) .eax,
   .mov .eax (.mem (argOp 3)), .store (at_ .edi nOff) .eax, .alu .test .eax (.reg .eax)]

/-- Load data block `b` at `esi`: its word `w` into slot `2w + b`. -/
def loadBlock (b : Nat) : List Instr :=
  (List.range 4).flatMap fun w => [.mov .eax (.mem (at_ .esi (16 * b + 4 * w))), st (2 * w + b) .eax]

/-- Load the last block into both halves of the state. -/
def loadOne : List Instr :=
  (List.range 4).flatMap fun w =>
    [.mov .eax (.mem (at_ .esi (4 * w))), st (2 * w) .eax, st (2 * w + 1) .eax]

/-- Store slots `2w + b` to data block `b` at `esi`. -/
def storeBlock (b : Nat) : List Instr :=
  (List.range 4).flatMap fun w => [movS .eax (2 * w + b), .store (at_ .esi (16 * b + 4 * w)) .eax]

/-- Load the data pointer and the count, and compare the count with 2. -/
def groupLoad : List Instr :=
  [.mov .esi (.mem (at_ .edi dOff)), .mov .ebp (.mem (at_ .edi nOff)), .alu .cmp .ebp (.imm 2)]

/-- Load one group (two blocks, or the last one) into slots `0 … 7`. -/
def loadGroup : Prog isa :=
  .seq (.block groupLoad) (.ite .ae (.block (loadBlock 0 ++ loadBlock 1)) (.block loadOne))

/-- Two blocks, and on to the next two. -/
def storeTwo : List Instr := storeBlock 0 ++ storeBlock 1 ++ [addI .esi 32, subI .ebp 2]

/-- The last block. -/
def storeOne : List Instr := storeBlock 0 ++ [subR .ebp .ebp]

/-- Store one group back, and the data pointer and the count (ZF is set
when none are left). -/
def storeGroup : Prog isa :=
  .seq (.block groupLoad)
    (.seq (.ite .ae (.block storeTwo) (.block storeOne))
      (.block [.store (at_ .edi dOff) .esi, .store (at_ .edi nOff) .ebp, .alu .test .ebp (.reg .ebp)]))

/-- One group of (up to) two blocks, through `crypt2`. -/
def blockGroup (crypt2 : Prog isa) : Prog isa := .seq loadGroup (.seq crypt2 storeGroup)

/-- The whole function, around `crypt2`. -/
def blocks (crypt2 : Prog isa) : Prog isa :=
  .seq (.block (saveRegs 4 ++ keySetup))
    (.seq (.loop (.block keyBody) .ae)
      (.seq (.block blocksSetup)
        (.seq (.ite .e (.block []) (.loop (blockGroup crypt2) .ne)) (.block restoreRegs))))

/-- `kp :=` the last round key. -/
def kpLast : List Instr := [movR kp .edi, addI kp (BitVec.ofNat 32 lastKey)]

/-- Compare `kp` with round key 1, `edi + lastKey + 32 - 32 rounds`. -/
def cmpFirst : List Instr :=
  [.mov .ebx (.mem (argOp 1))] ++ dbl .ebx 5 ++
  [movR .eax .edi, addI .eax (BitVec.ofNat 32 (lastKey + 32)), subR .eax .ebx, .alu .cmp kp (.reg .eax)]

/-- A middle round of the inverse cipher, with `kp` at the previous round
key; loops until `kp` is at round key 1. -/
def invRoundBody : List Instr :=
  [subI kp 32] ++ invShiftRows ++ invSboxCode ++ addRoundKey ++ invMixColumns ++ cmpFirst

/-- The last round of the inverse cipher, with round key 0. -/
def invLastRound : List Instr := [subI kp 32] ++ invShiftRows ++ invSboxCode ++ addRoundKey

/-- Decrypt the two blocks in slots `0 … 7` (as `ortho` takes them). -/
def decrypt2 : Prog isa :=
  .seq (.block (ortho ++ kpLast ++ addRoundKey))
    (.seq (.loop (.block invRoundBody) .ne) (.block (invLastRound ++ ortho)))

def encryptBlocks : Prog isa := blocks encrypt2
def decryptBlocks : Prog isa := blocks decrypt2

end VG.Impl.Aes.X86
