module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
public import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
public import VerifiedGarbage.Impl.CmacTripleDes.AArch64
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# Triple DES-CBC on AArch64

`dirCore d`, the scalar core: the block function
(`vg_triple_des_encrypt_block` or `vg_triple_des_decrypt_block`) called on
one 8-byte block (`cbcEncryptChained` here, which is not emitted: CBC
encryption is `TablesCbc.encrypt`, below).

Its slots: the block function's 64 (`x2`), the buffer's one block,
and a copy of the 384-byte schedule, which `prepare` makes so that nothing
the modes write can reach it. `crypt` points `x0`, `x1` and `x2` at the
copy, the buffer and the block function's slots, and restores the scratch
buffer's address (`sb`, which the block function overwrites) from `x2`,
which no instruction of the block function writes, and the return address
(`x30`, which the call overwrites) from `x26`. The call keeps `x23`, `x24`
and `x26` (callee-saved, and saved by the modes for their caller), which
carry the data's address, the blocks left and the return address, and
`x25`, where encryption keeps the IV's address, which the block function
never writes.

`batchCore d`, the batched core: the ECB functions' bitsliced batch
(`BitsliceNeon.batch d`, `Bitsliced.lean`) on a buffer of 128 blocks, for
the modes whose blocks are deciphered independently: `cbcDecryptChained`
(schedule = x0, iv = x1, data = x2, n = x3, scratch = x4), the modes'
generic CBC decryption that updates the chaining value
(`Impl/Modes/AArch64/CbcChained.lean`), and CFB64 decryption (`Fb.lean`),
each group of up to 128 blocks by one batch. Its slots are the buffer's 128
blocks, the batch's state words, on which the batch runs in place. The key
is the schedule where the caller passed it, at `x0`, which neither the
modes nor the batch write; `prepare` does nothing. `crypt` keeps the
scratch buffer's address (`sb` = `x5`, which the batch writes) in `x15`,
points `x4` at the buffer and calls the batch (`BitsliceNeon.batchCall`,
the return address kept in `x14`), which keeps `x23` and `x24` and writes
no register the calling convention preserves.

`tableCore`, the table core: CMAC's block (`CmacTripleDes.AArch64.block`,
the S-boxes by `tbl` from tables in vector registers) on one 8-byte block,
for the modes whose blocks each need the one before: OFB, CFB64 encryption,
CFB8 and the functions of a message's last piece (`Fb.lean`,
`FbFinal.lean`). Its slots: the block's 57 words (the spread round keys and
the callee-saved registers it saves and restores), then the buffer's one
block. `prepare` keeps the schedule's address, where the caller passed it,
in `x4`; `crypt` points `x14` at the schedule and `x15` at the scratch
buffer, takes the buffer's block into `x5` as a big-endian integer, runs
the block, stores `x5` back and restores `sb` (`x5`) from `x15`. The block
writes none of `x1`–`x4` nor `x28`: the modes keep the data's address and
the blocks left in `x2` and `x3`, where the arguments are, and the IV's
address in `x28`, and no value that must stay public is reloaded from the
scratch buffer.

The working space is the scratch buffer, which the artifact allocates on
the stack.
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Impl.Modes.AArch64 (copyW)
open VG.Spec.TripleDes (Direction)

/-- The core's buffer: one block, after the block function's slots. -/
def cbcBuf : Nat := 64

/-- The schedule's copy, after the buffer. -/
def schedSlot : Nat := 65

/-- The block function of the direction `d`. -/
def dirBlock : Direction → Prog isa
  | .encrypt => encryptBlock
  | .decrypt => decryptBlock

/-- A call of the block function of the direction `d`
(`vg_triple_des_encrypt_block` or `vg_triple_des_decrypt_block`). -/
def blockCall : Direction → Prog isa
  | .encrypt => .call "vg_triple_des_encrypt_block" encryptBlock
  | .decrypt => .call "vg_triple_des_decrypt_block" decryptBlock

/-- Triple DES's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Impl.Modes.AArch64.Core where
  prepare := .block ((List.range 48).flatMap (copyW .x6 sb .x0 (8 * schedSlot) 0))
  crypt := .seq (.block [.addImm .x .x0 sb (8 * schedSlot), .addImm .x .x1 sb (8 * cbcBuf), rr .x2 sb, rr .x26 .x30])
    (.seq (blockCall d) (.block [rr sb .x2, rr .x30 .x26]))
  slots := schedSlot + 48
  total := schedSlot + 60
  buf := cbcBuf
  lgG := 0
  bw := 1
  keyRegs := [.x0]
  dataReg := .x23
  leftReg := .x24

/-- The batched core's `crypt`: the batch of the direction `d` on the buffer. -/
def batchCrypt (d : Direction) : Prog isa :=
  .seq (.block [movR .x15 sb, movR .x4 sb]) (.seq (BitsliceNeon.batchCall d) (.block [movR sb .x15]))

/-- Triple DES's core for the modes whose blocks are independent, in the
direction `d`: 128 blocks by one bitsliced batch. -/
def batchCore (d : Direction) : Impl.Modes.AArch64.Core where
  prepare := .block []
  crypt := batchCrypt d
  slots := 128
  total := 140
  buf := 0
  lgG := 7
  bw := 1
  keyRegs := [.x0]
  dataReg := .x23
  leftReg := .x24

/-- The table core's buffer: one block, after the table block's 57 words. -/
def tableBuf : Nat := 57

/-- The table core's `crypt`: the buffer's block through CMAC's block. -/
def tableCrypt : Prog isa :=
  .seq (.block [movR .x14 .x4, movR .x15 sb, .ldr .x .x5 .x15 (8 * tableBuf), .rev .x5 .x5])
    (.seq CmacTripleDes.AArch64.block
      (.block [.rev .x5 .x5, .str .x .x5 .x15 (8 * tableBuf), movR sb .x15]))

/-- Triple DES's core for the modes whose blocks each need the one before:
one block by CMAC's block, with the S-box tables in vector registers. -/
def tableCore : Impl.Modes.AArch64.Core where
  prepare := .block [movR .x4 .x0]
  crypt := tableCrypt
  slots := tableBuf + 1
  total := tableBuf + 13
  buf := tableBuf
  lgG := 0
  bw := 1
  keyRegs := [.x0]
  dataReg := .x2
  leftReg := .x3

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).cbcEncryptChained ⟨.x1, .x2, .x3, .x4⟩ .x25

/-- `vg_triple_des_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (batchCore .decrypt).cbcDecryptChained ⟨.x1, .x2, .x3, .x4⟩

namespace TablesCbc

open VG.Impl.CmacTripleDes.AArch64 (mov prep enc chainIn)

/-- Ciphertext replaces the current plaintext and becomes the next IV. -/
def store : List Instr :=
  [.rev .x5 .x5, .str .x .x5 .x2 0, .str .x .x5 .x1 0,
   .addImm .x .x2 .x2 8, .subImm .x .x3 .x3 1]

/-- Reuse CMAC's rotated/spread layout and register-resident S-box tables.
Setup and round-key spreading happen once, before all blocks of the call. -/
def encrypt : Prog isa :=
  .seq (.block [mov .x14 .x0, mov .x15 .x4]) <|
  .ite (.zero .x .x3) (.block []) <|
  .seq prep <| .seq (.loop (.seq (.block chainIn) (.seq enc (.block store))) (.nonzero .x .x3))
    (.block VG.Impl.CmacTripleDes.AArch64.blockRestore)

end TablesCbc

end VG.Impl.TripleDes.AArch64
