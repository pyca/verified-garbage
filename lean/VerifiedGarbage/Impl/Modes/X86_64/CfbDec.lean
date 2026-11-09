module

public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# Batched CFB128 decryption on x86-64, for any block cipher with 16-byte blocks

`cfbDecryptBatched core regs`: CFB decryption with segments of a whole
block (SP 800-38A §6.3), which also replaces the IV with the block to
continue from, the last ciphertext block `Cₙ` (and leaves it unchanged if
`n = 0`), over a block cipher's core (`Core`, as for CTR), whose `crypt`
applies the forward cipher `CIPH_K` to the `G` blocks of its buffer.

Decryption's input blocks are the IV and the ciphertext blocks before the
last, `Iⱼ = Cⱼ₋₁`, which are all known before any block is decrypted: each
group of up to `G` blocks is enciphered at once, as CBC decryption's
(`Cbc.lean`), not one block at a time as the modes' generic CFB (`Fb.lean`).
The mode's chaining value's slots (`hiSlot`) hold `Cⱼ₋₁` from one group to
the next, as CBC decryption's do.

* The entry, the IV to the chaining value's slots and the last block of the
  data to the IV, as CBC decryption that updates the chaining value's
  (`cbcDecryptChained`, `CbcChained.lean`): the IV's address, `r.ctr`, is
  needed only there.
* Each group of `c = min(G, left)` blocks at `A`: the chaining value to the
  buffer's first block, the group's first `c - 1` ciphertext blocks to the
  rest (`copyBlocks`, from `rbx` to `rax`), and its last, now at `rbx`, to
  the chaining value's slots; the core's `crypt` enciphers the buffer, which
  is XORed into the ciphertext blocks (`xorBlocks`, as for CTR), making them
  the plaintext blocks.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

namespace Core

variable (c : Core)

/-- The buffer's second block to `rax`, the group's ciphertext to `rbx`,
and one fewer block to copy in `rcx`; ZF is set when there is none. -/
def cfbDecGatherArgs : List Instr :=
  [movR .rax sb, .alu .add .rax (.imm (BitVec.ofNat 32 (8 * c.buf + 16))), movR .rbx c.dataReg,
   .alu .sub .rcx (.imm 1)]

/-- The group's `rcx` input blocks to the buffer: the chaining value, then
the group's ciphertext blocks but its last, which becomes the chaining
value (through `rbp`). -/
def cfbDecGather : Prog isa :=
  .seq (.block ((List.range 2).flatMap (copyW .rbp sb sb (8 * c.buf) (8 * c.hiSlot)) ++ c.cfbDecGatherArgs))
    (.seq (.ite .e (.block []) c.copyBlocks)
      (.block ((List.range 2).flatMap (copyW .rbp sb .rbx (8 * c.hiSlot) 0))))

/-- One group: its input blocks to the buffer, enciphered, and XORed into
its ciphertext blocks. -/
def cfbDecGroup : Prog isa :=
  .seq c.groupCount (.seq c.cfbDecGather (.seq c.crypt
    (.seq c.groupCount (.seq (.block c.xorArgs) (.seq xorBlocks (.block c.advance))))))

/-- The whole function: the entry, the IV to the chaining value, the last
block to the IV, the key, the groups. -/
def cfbDecryptBatched (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r ++ c.cbcSetup r))
    (.seq (c.cbcLastToIv r)
      (.seq (.block (c.ctrArgs r))
        (.seq c.prepare
          (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
            (.seq (.ite .e (.block []) (.loop c.cfbDecGroup .ne)) (.block c.restoreRegs))))))

end Core

end VG.Impl.Modes.X86_64
