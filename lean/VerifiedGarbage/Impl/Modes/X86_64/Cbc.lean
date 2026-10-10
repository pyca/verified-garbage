import VerifiedGarbage.Impl.Modes.X86_64.Ctr

/-!
# CBC decryption on x86-64, for any block cipher with 16-byte blocks

`cbcDecrypt core regs`: CBC decryption (SP 800-38A §6.2) over a block
cipher's core (`Core`, as for CTR), whose `crypt` here applies the inverse
cipher `CIPH⁻¹_K` to the `G` blocks of its buffer. Each group of up to `G`
blocks is decrypted at once: decryption, unlike encryption, needs no block's
result for the next.

The mode's 8 slots hold the callee-saved registers (`savedSlot`) and the
chaining value `Cⱼ₋₁` (`hiSlot`, `loSlot`: its bytes 0–7 and 8–15).

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
  [.mov .rax (.mem (at_ r.ctr 0)), .mov .rbx (.mem (at_ r.ctr 8)), st c.hiSlot .rax, st c.loSlot .rbx]

/-- Copy `rcx` blocks at `rbx` to `rax` (through `rbp`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.mov .rbp (.mem (at_ .rbx 0)), .store (at_ .rax 0) .rbp,
      .mov .rbp (.mem (at_ .rbx 8)), .store (at_ .rax 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)]) .ne

/-- Word `w` (0 or 1) of a block: the decrypted word at `rax` XORed with the
chaining value's, back to `rax`; the ciphertext's word at `rbx` to the
chaining value; the plaintext's from `rax` to `rbx`. -/
def unchainWord (w : Nat) : List Instr :=
  [.mov .rbp (.mem (at_ .rax (8 * w))), xorS .rbp (c.hiSlot + w), .store (at_ .rax (8 * w)) .rbp,
   .mov .rbp (.mem (at_ .rbx (8 * w))), st (c.hiSlot + w) .rbp,
   .mov .rbp (.mem (at_ .rax (8 * w))), .store (at_ .rbx (8 * w)) .rbp]

/-- `rcx` blocks: the decryptions at `rax`, the ciphertexts at `rbx`. -/
def unchainBlocks : Prog isa :=
  .loop (.block (c.unchainWord 0 ++ c.unchainWord 1 ++
    ([.alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr))) .ne

/-- One group: its ciphertext blocks to the buffer, decrypted, and the
plaintext blocks back to the data. -/
def cbcDecGroup : Prog isa :=
  .seq c.groupCount (.seq (.block c.xorArgs) (.seq copyBlocks (.seq c.crypt
    (.seq c.groupCount (.seq (.block c.xorArgs) (.seq c.unchainBlocks (.block c.advance)))))))

/-- The whole function: the chaining value, the key, then the groups. -/
def cbcDecrypt (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.cbcSetup r ++ c.ctrArgs r))
    (.seq c.prepare
      (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
        (.seq (.ite .e (.block []) (.loop c.cbcDecGroup .ne)) (.block c.restoreRegs))))

end Core

end VG.Impl.Modes.X86_64
