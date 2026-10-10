import VerifiedGarbage.Impl.Modes.X86_64.Ctr

/-!
# CBC decryption on x86-64, for any block cipher with blocks of 8 or 16 bytes

`cbcDecrypt core regs`: CBC decryption (SP 800-38A §6.2) over a block
cipher's core (`Core`, as for CTR), whose `crypt` here applies the inverse
cipher `CIPH⁻¹_K` to the `G` blocks of its buffer. Each group of up to `G`
blocks is decrypted at once: decryption, unlike encryption, needs no block's
result for the next.

Blocks are `bw` 8-byte words, moved a word at a time (`copyW`, `xorW`).
The mode's 8 slots hold the callee-saved registers (`savedSlot`) and the
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

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

namespace Core

variable (c : Core)

/-- The IV at `r.ctr` to the chaining value's slots. -/
def cbcSetup (r : CtrRegs) : List Instr :=
  (List.range c.bw).flatMap (copyW .rax sb r.ctr (8 * c.hiSlot) 0)

/-- Past a block at `rax` and `rbx`, one fewer in `rcx`. -/
def nextBlock : List Instr :=
  [.alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.bw))), .alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c.bw))),
   .alu .sub .rcx (.imm 1)]

/-- Copy `rcx` blocks at `rbx` to `rax` (through `rbp`). -/
def copyBlocks : Prog isa := .loop (.block ((List.range c.bw).flatMap (copyW .rbp .rax .rbx 0 0) ++ c.nextBlock)) .ne

/-- `rcx` blocks: the decryptions at `rax`, the ciphertexts at `rbx`. Each
block: the chaining value XORed into the decryption, the ciphertext to the
chaining value, the plaintext to the data (through `rbp`). -/
def unchainBlocks : Prog isa :=
  .loop (.block ((List.range c.bw).flatMap (xorW .rbp .rax sb 0 (8 * c.hiSlot)) ++
    (List.range c.bw).flatMap (copyW .rbp sb .rbx (8 * c.hiSlot) 0) ++
    (List.range c.bw).flatMap (copyW .rbp .rbx .rax 0 0) ++ c.nextBlock)) .ne

/-- One group: its ciphertext blocks to the buffer, decrypted, and the
plaintext blocks back to the data. -/
def cbcDecGroup : Prog isa :=
  .seq c.groupCount (.seq (.block c.xorArgs) (.seq c.copyBlocks (.seq c.crypt
    (.seq c.groupCount (.seq (.block c.xorArgs) (.seq c.unchainBlocks (.block c.advance)))))))

/-- The whole function: the chaining value, the key, then the groups. -/
def cbcDecrypt (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.cbcSetup r ++ c.ctrArgs r))
    (.seq c.prepare
      (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
        (.seq (.ite .e (.block []) (.loop c.cbcDecGroup .ne)) (.block c.restoreRegs))))

end Core

end VG.Impl.Modes.X86_64
