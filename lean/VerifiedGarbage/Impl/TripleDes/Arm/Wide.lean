module

public import VerifiedGarbage.Impl.TripleDes.Arm.Bitsliced

/-!
# Triple DES-CBC and -CFB64 decryption on ARMv7, a batch of blocks at a time

`cbcDecrypt` and `cfbDecrypt` (schedule = r0, iv = r1, data = r2, n = r3,
scratch = [sp]), whose blocks are deciphered independently: the code of
`vg_triple_des_cbc_decrypt_chained` and `vg_triple_des_cfb64_decrypt` with
their working space, 1024 bytes, as an argument. They are bitsliced ECB's
batches (`Bitsliced.lean`) of up to 32 blocks, with its working space, its
transposition and its passes, but for what goes into the state words and
what comes out of them:

* CBC decryption deciphers the batch's blocks, and stores each XORed with
  the block before it (the chaining value at `iv` for the first), which it
  keeps in `r9` and `r10` from one block to the next, as it reads each
  ciphertext block before it stores over it; the last one is the next
  chaining value.
* CFB decryption enciphers the block before each of the batch's blocks (the
  chaining value for the first), stores the last block as the next
  chaining value, and XORs the results into the blocks.

The arguments are moved to where ECB's batch has them: the schedule in
`r0`, the data in `r1`, the blocks left in `r2`, the working space in `r3`;
the chaining value's address is in `r8`, and in the working space
(`ivOff`) while every register is in use.
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm.Wide

open VG.Arm VG.Impl.TripleDes.Arm.Bitslice

/-- The chaining value's address, in the working space. -/
def ivOff : Nat := 356

/-- The registers the code saves, and their offsets in the working space,
past the words the batches use. -/
def saved : List (Reg × Nat) :=
  [(.r4, 360), (.r5, 364), (.r6, 368), (.r7, 372), (.r8, 376), (.r9, 380), (.r10, 384), (.r11, 388),
   (.lr, 392)]

/-- The arguments where the batches have them; Z is set if there are no blocks. -/
def args : List Instr :=
  [.mov .r8 (.reg .r1), .mov .r1 (.reg .r2), .mov .r2 (.reg .r3), .mov .r3 (.reg .r12), .cmp .r2 (.imm 0)]

/-- The working space's address, the caller's registers saved in it, and
the arguments where the batches have them. -/
def enter : Prog isa :=
  .seq (.block [.ldrSp .r12 0]) (.seq (.block (saved.map fun p => .str p.1 .r12 p.2)) (.block args))

/-- The caller's registers back. -/
def restore : List Instr := saved.map fun p => .ldr p.1 base p.2

/-- The function: the batches `batch`, if there are blocks. -/
def wide (batch : Prog isa) : Prog isa :=
  .seq enter (.seq (.ite .eq (.block []) (.loop batch .ne)) (.block restore))

/-- The chaining value into `r9` and `r10`, and back. -/
def prevLoad : List Instr := [.ldr .r9 .r8 0, .ldr .r10 .r8 4]
def prevStore : List Instr := [.str .r9 .r8 0, .str .r10 .r8 4]

/-- The chaining value's address to the working space, and back. -/
def ivStash : List Instr := [.str .r8 base ivOff]
def ivUnstash : List Instr := [.ldr .r8 base ivOff]

/-- The state words through the transposition, the three passes of the
direction `d` and the transposition back, with the batch's registers in the
working space meanwhile. -/
def kernel (d : VG.Spec.TripleDes.Direction) : Prog isa :=
  .seq (.block stash) (.seq (.block ivStash) (.seq (.block transpose) (.seq (passes d)
    (.seq (.block transpose) (.seq (.block unstash) (.block ivUnstash))))))

/-! ## CBC decryption -/

/-- A deciphered block, XORed with the block before it, over its
ciphertext, which is the block before the next. -/
def cbcOutBody : List Instr :=
  [.ldr .r11 .r5 0, .ldr .lr .r5 4,
   .ldr .r7 .r4 0, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 0,
   .ldr .r7 .r4 128, .dp .eor .r7 .r7 (.reg .r10), .str .r7 .r5 4,
   .mov .r9 (.reg .r11), .mov .r10 (.reg .lr)] ++ copyNext

/-- The state words back to the batch's blocks, each XORed with the block
before it, and the last ciphertext block to the chaining value. -/
def cbcOut : Prog isa :=
  .seq (.block copyStart) (.seq (.block prevLoad)
    (.seq (.loop (.block cbcOutBody) .ne) (.block prevStore)))

/-- One batch of CBC decryption. -/
def cbcBatch : Prog isa :=
  .seq batchCount (.seq copyIn (.seq (kernel .decrypt) (.seq cbcOut (.block advance))))

def cbcDecrypt : Prog isa := wide cbcBatch

/-! ## CFB decryption -/

/-- The block before a block into the state words, and the block. -/
def cfbInBody : List Instr :=
  [.str .r9 .r4 0, .str .r10 .r4 128, .ldr .r9 .r5 0, .ldr .r10 .r5 4] ++ copyNext

/-- The chaining value and the batch's blocks but the last into the state
words, and the last to the chaining value. -/
def cfbIn : Prog isa :=
  .seq (.block copyStart) (.seq (.block prevLoad)
    (.seq (.loop (.block cfbInBody) .ne) (.block prevStore)))

/-- A state word pair XORed into a block. -/
def cfbOutBody : List Instr :=
  [.ldr .r7 .r5 0, .ldr .r9 .r4 0, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 0,
   .ldr .r7 .r5 4, .ldr .r9 .r4 128, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 4] ++ copyNext

/-- The state words XORed into the batch's blocks. -/
def cfbOut : Prog isa := .seq (.block copyStart) (.loop (.block cfbOutBody) .ne)

/-- One batch of CFB decryption. -/
def cfbBatch : Prog isa :=
  .seq batchCount (.seq cfbIn (.seq (kernel .encrypt) (.seq cfbOut (.block advance))))

def cfbDecrypt : Prog isa := wide cfbBatch

end VG.Impl.TripleDes.Arm.Wide
