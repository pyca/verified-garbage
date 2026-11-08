module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Blocks

/-! # Source-prefix readers for the shared POWER8 GCM batch -/

@[expose] public section

namespace VG.Impl.AesGcm.PPC64LE.SplitBlocks
open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks
open VG.Impl.Aes.PPC64LE.Crypto (mov storePerm)

-- r17 points to the unconsumed external prefix; r19 counts its blocks.
-- Only the batch crossing its end needs a choice for each vector load.
def partialLoad (i : Nat) : Prog isa :=
 .seq (.block [.subi .r12 .r19 (i+1),.lsr .d .r12 .r12 63])
 (.ite (.zero .d .r12) (.block [.lxvd2x (dataReg i) .r17 (dataOffset i)])
   (.block [.lxvd2x (dataReg i) .r6 (dataOffset i)]))

def partialLoadsFrom : Nat → Nat → Prog isa
 | _,0 => .block []
 | start,count+1 => .seq (partialLoad start) (partialLoadsFrom (start+1) count)

def load : Prog isa :=
 .ite (.zero .d .r19) (.block dataLoad)
 (.seq (.block [.lsr .d .r12 .r19 3])
 (.ite (.nonzero .d .r12)
   (.block (dataLoadAt .r17 ++ [.addi .r17 .r17 128,.subi .r19 .r19 8]))
   (.seq (partialLoadsFrom 0 8)
     (.block [.lsl .r12 .r19 4,.add .r17 .r17 .r12,.li .r19 0]))))

/-- Decryption's store step for block `i`, read from the source: the
ciphertext in register order, then the plaintext (its XOR with the keystream
in the state register) in the data register, and the ciphertext again in the
state register, which the batch then hashes. -/
def decMixStep (i : Nat) : List Instr :=
 [.vop (.perm (dataReg i) (dataReg i) (dataReg i) .v19),
  .vop (.logic .xor (dataReg i) (dataReg i) (reg i)),
  .vop (.logic .xor (reg i) (reg i) (dataReg i))]

def decMix : List Instr := (List.range 8).flatMap decMixStep

/-- Each plaintext stored at `r6`. -/
def decWrite : List Instr :=
 (List.range 8).flatMap (fun i => storePerm (dataReg i) (dataReg i) .r6 (dataOffset i))

def decStoresFinish : List Instr := decMix ++ decWrite ++ [.addi .r6 .r6 128,.subi .r7 .r7 8]

/-- The store step: encryption's (`dec = false`), which writes and hashes
the ciphertext it makes, or decryption's, which writes the plaintext and
hashes the ciphertext it read. -/
def finishOf (dec : Bool) : List Instr := bif dec then decStoresFinish else storesFinish

def batchOf (dec : Bool) : Prog isa := batchWithStore (.seq load (.block (finishOf dec)))

def codeOf (dec : Bool) : Prog isa := codeWith (batchOf dec)

def batch : Prog isa := batchOf false

def code : Prog isa := codeOf false

def decCode : Prog isa := codeOf true

-- The kernel leaves these registers available to track the external prefix.
-- Their caller values fit between the core's spills and its tables.
def extraSaved : List (Reg × Nat) := [(.r17,152),(.r19,160)]

def argsHead : List Instr := [.addSp .r12 0,.load .d .r11 .r12 96]

def argsConfig : List Instr :=
 [mov .r17 .r7,mov .r19 .r8,mov .r7 .r9,mov .r8 .r10,mov .r9 .r11]

def argsRest : List Instr := extraSaved.map (fun (r,o) => .store .d r .r11 o) ++ argsConfig

def bulkOf (dec : Bool) : Prog isa := .seq (.block bulkArgs) (.seq (codeOf dec) (.block bulkRest))

def bulk : Prog isa := bulkOf false

-- Only short inputs, or at most seven blocks after the bulk loop, need
-- their external prefix copied before the existing CTR/GHASH tail.
def copyStep : List Instr := [.lxvd2x U .r17 .r0,.stxvd2x U .r11 .r0,
 .addi .r17 .r17 16,.addi .r11 .r11 16,.subi .r19 .r19 1]

def copyPrefix : Prog isa := .ite (.zero .d .r19) (.block [])
 (.seq (.block [mov .r11 .r30,.li .r0 0])
 (.loop (.block copyStep) (.nonzero .d .r19)))

def restoreExtra : List Instr := extraSaved.map (fun (r,o) => .load .d r .r31 o)

def maybeBulkOf (dec : Bool) : Prog isa := .ite (.zero .d .r12) (.block []) (bulkOf dec)

def maybeBulk : Prog isa := maybeBulkOf false

def tailOf (dec : Bool) : Prog isa := bif dec then decTail else tail

def bodyOf (dec : Bool) : Prog isa := .seq (.block wrapperEntry) (.seq (maybeBulkOf dec)
 (.seq copyPrefix (.seq (.block restoreExtra) (.seq (tailOf dec) (.block wrapperExit)))))

def body : Prog isa := bodyOf false

def head : Prog isa := .block argsHead

def restOf (dec : Bool) : Prog isa := .seq (.block argsRest) (bodyOf dec)

def rest : Prog isa := restOf false

def decRest : Prog isa := restOf true

/-- Nine-argument whole-block helper; `scratch` is at the incoming `sp+96`.
Restore the extra saves before the leaf calls reuse the core's scratch. -/
def cryptOf (dec : Bool) : Prog isa := .ite (.zero .d .r10) (.block [])
 (.seq head (restOf dec))

/-- `vg_aes_gcm_encrypt_blocks_split`. -/
def encrypt : Prog isa := cryptOf false

/-- `vg_aes_gcm_decrypt_blocks_split`: the same, decrypting, and hashing
the ciphertext it reads. -/
def decrypt : Prog isa := cryptOf true

/-- `vg_aes_gcm_decrypt_blocks_to(ctx, rounds, state, src, n, dst, dst_n,
scratch)`: `decrypt` with every block in the source and its eight arguments
in registers, moved to `decrypt`'s: the hash accumulator at `state` and the
counter block at `state + 32`, `src_n = n`, and `scratch` in `r11`. -/
def toArgs : List Instr :=
 [mov .r11 .r10,mov .r10 .r7,mov .r9 .r8,mov .r8 .r7,mov .r7 .r6,mov .r6 .r5,.addi .r5 .r5 32]

def decryptTo : Prog isa := .ite (.zero .d .r7) (.block []) (.seq (.block toArgs) decRest)

end VG.Impl.AesGcm.PPC64LE.SplitBlocks
