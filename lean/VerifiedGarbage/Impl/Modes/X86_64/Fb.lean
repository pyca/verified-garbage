import VerifiedGarbage.Impl.Modes.X86_64.Ctr
import VerifiedGarbage.Impl.Modes.FbMode

/-!
# OFB and CFB on x86-64, for any block cipher with blocks of 8 or 16 bytes

`fb core mode regs`: OFB (SP 800-38A §6.4) or CFB with segments of a
whole block (§6.3, encryption or decryption) over a block cipher's core
(`Core`, as for CTR), whose `crypt` applies the forward cipher `CIPH_K` to
the `G` blocks of its buffer. Each block's input block is the previous
block's output (OFB) or ciphertext (CFB), so each call of `crypt` enciphers
one block, in the buffer's first, and the other `G - 1` are wasted.

The input block is never held apart from the core's buffer: before block
`j` the buffer's first block is the input block `Iⱼ` (the IV for `j = 0`);
`crypt` makes it `Oⱼ = CIPH_K(Iⱼ)`, which is XORed into the data, and the
buffer is made `Iⱼ₊₁`:

* OFB: `Iⱼ₊₁ = Oⱼ`, already there;
* CFB encryption: `Iⱼ₊₁ = Cⱼ = Pⱼ ⊕ Oⱼ`, copied back from the data;
* CFB decryption: `Iⱼ₊₁ = Cⱼ`, the block of the data before the XOR, which
  is `Oⱼ ⊕ Pⱼ`: the data, now `Pⱼ`, is XORed back into the buffer.

After the last block the buffer holds `Iₙ₊₁`, the block to continue from,
which replaces the IV. The mode's slots hold the callee-saved registers
(`savedSlot`) and the IV's address (`hiSlot`), which `prepare` and `crypt`
may not keep in a register.

* The scratch buffer moves to `sb`, the callee-saved registers and the IV's
  address to the mode's slots. The data's address and `n` move to
  `dataReg` and `leftReg`.
* `core.prepare` makes the key ready.
* The IV to the buffer, the blocks, and the buffer back to the IV.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64
open VG.Impl.Modes (FbMode)

namespace Core

variable (c : Core)

/-- The scratch buffer to `sb`, the callee-saved registers and the IV's
address (`r.ctr`) to the mode's slots, the data's address and `n` to
`dataReg` and `leftReg`. -/
def fbEntry (r : CtrRegs) : List Instr :=
  c.ctrEntry r ++ ([st c.hiSlot r.ctr] : List Instr) ++ c.ctrArgs r

/-- The IV to the buffer's first block. -/
def fbLoad : List Instr :=
  ([movS .rax c.hiSlot] : List Instr) ++ (List.range c.bw).flatMap (copyW .rbp sb .rax (8 * c.buf) 0)

/-- The buffer's first block back to the IV. -/
def fbStore : List Instr :=
  ([movS .rax c.hiSlot] : List Instr) ++ (List.range c.bw).flatMap (copyW .rbp .rax sb 0 (8 * c.buf))

/-- `Oⱼ`, in the buffer's first block, XORed into the block at `dataReg`, and
the buffer made `Iⱼ₊₁`. -/
def fbOp : FbMode → List Instr
  | .ofb => (List.range c.bw).flatMap (xorW .rax c.dataReg sb 0 (8 * c.buf))
  | .cfbEnc => (List.range c.bw).flatMap (xorW .rax c.dataReg sb 0 (8 * c.buf)) ++
      (List.range c.bw).flatMap (copyW .rax sb c.dataReg (8 * c.buf) 0)
  | .cfbDec => (List.range c.bw).flatMap (xorW .rax c.dataReg sb 0 (8 * c.buf)) ++
      (List.range c.bw).flatMap (xorW .rax sb c.dataReg (8 * c.buf) 0)

/-- On to the next block; ZF is set when none is left. -/
def fbNext : List Instr :=
  [.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw))), .alu .sub c.leftReg (.imm 1)]

/-- One block: its input block enciphered in the buffer, XORed into the
data, and the next input block. The IV's address is loaded into `rcx` and
stored back around the data's stores, so that the constant-time analysis,
which forgets what memory held after a store to the data, knows it is
public. -/
def fbBlock (m : FbMode) : Prog isa :=
  .seq c.crypt (.block (([movS .rcx c.hiSlot] : List Instr) ++ c.fbOp m ++ ([st c.hiSlot .rcx] : List Instr) ++
    c.fbNext))

/-- The whole function: the entry, the key, the IV to the buffer, the
blocks, and the block to continue from back to the IV. -/
def fb (m : FbMode) (r : CtrRegs) : Prog isa :=
  .seq (.block (c.fbEntry r))
    (.seq c.prepare
      (.seq (.block (c.fbLoad ++ ([.alu .test c.leftReg (.reg c.leftReg)] : List Instr)))
        (.seq (.ite .e (.block []) (.loop (c.fbBlock m) .ne)) (.block (c.fbStore ++ c.restoreRegs)))))

end Core

end VG.Impl.Modes.X86_64
