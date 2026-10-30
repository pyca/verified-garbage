module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
public import VerifiedGarbage.Impl.CmacTripleDes.AArch64
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# Triple DES-CBC on AArch64

`cbcEncryptChained` and `cbcDecryptChained` (schedule = x0, iv = x1,
data = x2, n = x3, scratch = x4): the modes' generic CBC that updates the
chaining value (`Impl/Modes/AArch64/CbcChained.lean`) over calls of the scalar block function
(`vg_triple_des_encrypt_block` or `vg_triple_des_decrypt_block`), one 8-byte
block at a time, with the working space in the scratch buffer, which the
artifact allocates on the stack.

The core's slots: the block function's 64 (`x2`), the buffer's one block,
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
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (sb)
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

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).cbcEncryptChained ⟨.x1, .x2, .x3, .x4⟩ .x25

/-- `vg_triple_des_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).cbcDecryptChained ⟨.x1, .x2, .x3, .x4⟩

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
