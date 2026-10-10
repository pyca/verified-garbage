import VerifiedGarbage.Impl.Modes.AArch64.Ctr

/-!
# CBC decryption on AArch64, for any block cipher with blocks of 8 or 16 bytes

`cbcDecrypt core regs`: CBC decryption (SP 800-38A §6.2) over a block
cipher's core (`Core`, as for CTR), whose `crypt` here applies the inverse
cipher `CIPH⁻¹_K` to the `G` blocks of its buffer. Each group of up to `G`
blocks is decrypted at once: decryption, unlike encryption, needs no block's
result for the next. As on x86-64 (`Impl/Modes/X86_64/Cbc.lean`).

Blocks are `bw` 8-byte words, moved a word at a time (`copyW`, `xorW`).
The mode's slots hold the callee-saved registers (`savedSlot`) and the
chaining value `Cⱼ₋₁` (`hiSlot`, and `loSlot` for a second word).

* The scratch buffer moves to `sb`, the callee-saved registers to the
  mode's slots, the IV (`r.ctr`, only read) to the chaining value's. The
  data's address and `n` move to `dataReg` and `leftReg`.
* `core.prepare` makes the key ready.
* Each group of up to `G` blocks is copied to the core's buffer, `core.crypt`
  decrypts it there, and then, block by block: `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`
  is formed in the buffer, `Cⱼ` (still in the data) becomes the chaining
  value, and `Pⱼ` replaces it in the data.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

namespace Core

variable (c : Core)

/-- The IV at `r.ctr` to the chaining value's slots. -/
def cbcSetup (r : CtrRegs) : List Instr :=
  (List.range c.bw).flatMap (copyW .x6 sb r.ctr (8 * c.hiSlot) 0)

/-- Past a block at `x14` and `x15`, one fewer in `x17`. -/
def nextBlock : List Instr :=
  [.addImm .x .x14 .x14 (8 * c.bw), .addImm .x .x15 .x15 (8 * c.bw), .subImm .x .x17 .x17 1]

/-- Copy `x17` blocks at `x15` to `x14` (through `x8`). -/
def copyBlocks : Prog isa :=
  .loop (.block ((List.range c.bw).flatMap (copyW .x8 .x14 .x15 0 0) ++ c.nextBlock)) (.nonzero .x .x17)

/-- `x17` blocks: the decryptions at `x14`, the ciphertexts at `x15`. Each
block: the chaining value XORed into the decryption, the ciphertext to the
chaining value, the plaintext to the data (through `x8`, `x9`). -/
def unchainBlocks : Prog isa :=
  .loop (.block ((List.range c.bw).flatMap (xorW .x8 .x9 .x14 sb 0 (8 * c.hiSlot)) ++
    (List.range c.bw).flatMap (copyW .x8 sb .x15 (8 * c.hiSlot) 0) ++
    (List.range c.bw).flatMap (copyW .x8 .x15 .x14 0 0) ++ c.nextBlock)) (.nonzero .x .x17)

/-- One group: its ciphertext blocks to the buffer, decrypted, and the
plaintext blocks back to the data. -/
def cbcDecGroup : Prog isa :=
  .seq c.groupCount (.seq (.block c.xorArgs) (.seq c.copyBlocks (.seq c.crypt
    (.seq c.groupCount (.seq (.block c.xorArgs) (.seq c.unchainBlocks (.block c.advance)))))))

/-- The whole function: the chaining value, the key, then the groups. -/
def cbcDecrypt (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.cbcSetup r ++ c.ctrArgs r))
    (.seq c.prepare
      (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop c.cbcDecGroup (.nonzero .x c.leftReg)))
        (.block c.restoreRegs)))

end Core

end VG.Impl.Modes.AArch64
