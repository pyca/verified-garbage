import VerifiedGarbage.Impl.Modes.AArch64.Ctr
import VerifiedGarbage.Impl.Modes.FbMode

/-!
# OFB and CFB on AArch64, for any block cipher with blocks of 8 or 16 bytes

`fb core mode regs iv`: OFB (SP 800-38A §6.4) or CFB with segments of a
whole block (§6.3, encryption or decryption) over a block cipher's core
(`Core`, as for CTR), whose `crypt` applies the forward cipher `CIPH_K` to
the `G` blocks of its buffer. As on x86-64 (`Impl/Modes/X86_64/Fb.lean`):
each call of `crypt` enciphers one block, in the buffer's first, and the
other `G - 1` are wasted.

The input block is never held apart from the core's buffer: before block
`j` the buffer's first block is the input block `Iⱼ` (the IV for `j = 0`);
`crypt` makes it `Oⱼ = CIPH_K(Iⱼ)`, which is XORed into the data, and the
buffer is made `Iⱼ₊₁`:

* OFB: `Iⱼ₊₁ = Oⱼ`, already there;
* CFB encryption: `Iⱼ₊₁ = Cⱼ = Pⱼ ⊕ Oⱼ`, copied back from the data;
* CFB decryption: `Iⱼ₊₁ = Cⱼ`, the block of the data before the XOR, which
  is `Oⱼ ⊕ Pⱼ`: the data, now `Pⱼ`, is XORed back into the buffer.

After the last block the buffer holds the block to continue from, which
replaces the IV. AArch64's taint analysis takes all memory to be secret, so
the IV's address, which must stay public, is kept in the register `iv`
throughout: one the core neither writes nor uses (each adapter chooses it,
and proves the core keeps it), and none of the modes' own. If it is a
callee-saved register, the mode's slots keep its value for the caller, as
they keep the others'.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64
open VG.Impl.Modes (FbMode)

namespace Core

variable (c : Core)

/-- The scratch buffer to `sb`, the callee-saved registers to the mode's
slots, the IV's address (`r.ctr`) to `iv`, the data's address and `n` to
`dataReg` and `leftReg`. -/
def fbEntry (r : CtrRegs) (iv : Reg) : List Instr :=
  c.ctrEntry r ++ ([movR iv r.ctr] : List Instr) ++ c.ctrArgs r

/-- The IV to the buffer's first block. -/
def fbLoad (iv : Reg) : List Instr := (List.range c.bw).flatMap (copyW .x6 sb iv (8 * c.buf) 0)

/-- The buffer's first block back to the IV. -/
def fbStore (iv : Reg) : List Instr := (List.range c.bw).flatMap (copyW .x6 iv sb 0 (8 * c.buf))

/-- `Oⱼ`, in the buffer's first block, XORed into the block at `dataReg`, and
the buffer made `Iⱼ₊₁`. -/
def fbOp : FbMode → List Instr
  | .ofb => (List.range c.bw).flatMap (xorW .x6 .x7 c.dataReg sb 0 (8 * c.buf))
  | .cfbEnc => (List.range c.bw).flatMap (xorW .x6 .x7 c.dataReg sb 0 (8 * c.buf)) ++
      (List.range c.bw).flatMap (copyW .x6 sb c.dataReg (8 * c.buf) 0)
  | .cfbDec => (List.range c.bw).flatMap (xorW .x6 .x7 c.dataReg sb 0 (8 * c.buf)) ++
      (List.range c.bw).flatMap (xorW .x6 .x7 sb c.dataReg (8 * c.buf) 0)

/-- On to the next block. -/
def fbNext : List Instr :=
  [.addImm .x c.dataReg c.dataReg (8 * c.bw), .subImm .x c.leftReg c.leftReg 1]

/-- One block: its input block enciphered in the buffer, XORed into the
data, and the next input block. -/
def fbBlock (m : FbMode) : Prog isa := .seq c.crypt (.block (c.fbOp m ++ c.fbNext))

/-- The whole function: the entry, the key, the IV to the buffer, the
blocks, and the block to continue from back to the IV. -/
def fb (m : FbMode) (r : CtrRegs) (iv : Reg) : Prog isa :=
  .seq (.block (c.fbEntry r iv))
    (.seq c.prepare
      (.seq (.block (c.fbLoad iv))
        (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop (c.fbBlock m) (.nonzero .x c.leftReg)))
          (.block (c.fbStore iv ++ c.restoreRegs)))))

end Core

end VG.Impl.Modes.AArch64
