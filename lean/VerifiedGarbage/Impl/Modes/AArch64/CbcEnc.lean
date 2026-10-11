module

public import VerifiedGarbage.Impl.Modes.AArch64.Ctr

/-!
# CBC encryption on AArch64, for any block cipher with 16-byte blocks

`cbcEncrypt core regs`: CBC encryption (SP 800-38A §6.2) over a block
cipher's core (`Core`, as for CTR), whose `crypt` applies the forward cipher
`CIPH_K` to the `G` blocks of its buffer. Encryption is sequential: each
block's input is the previous block's output, so each call of `crypt`
encrypts one block, in the buffer's first, and the other `G - 1` are wasted.
As on x86-64 (`Impl/Modes/X86_64/CbcEnc.lean`).

The chaining value is never held apart from the data: the IV, which is only
read, is XORed into the first block at entry, and after block `j` is
encrypted in place its ciphertext `Cⱼ` is XORed into block `j + 1`. Each
block of the data is thus `Pⱼ ⊕ Cⱼ₋₁` when its turn comes, and only the
data's address and the blocks left, in `dataReg` and `leftReg`, are carried
across `crypt`.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

@[expose] public section

namespace VG.Impl.Modes.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

namespace Core

variable (c : Core)

/-- The IV at `r.ctr` XORed into the first block at `r.data`, unless `r.n`
is zero. -/
def cbcWhiten (r : CtrRegs) : Prog isa :=
  .ite (.zero .x r.n) (.block [])
    (.block [.ldr .x .x6 r.data 0, .ldr .x .x7 r.ctr 0, eorR .x6 .x6 .x7, .str .x .x6 r.data 0,
      .ldr .x .x6 r.data 8, .ldr .x .x7 r.ctr 8, eorR .x6 .x6 .x7, .str .x .x6 r.data 8])

/-- The block at `dataReg` to the buffer's first. -/
def encIn : List Instr :=
  [.ldr .x .x6 c.dataReg 0, stS c.buf .x6, .ldr .x .x6 c.dataReg 8, stS (c.buf + 1) .x6]

/-- The buffer's first block back to `dataReg`, and one block fewer left. -/
def encOut : List Instr :=
  [ldS .x6 c.buf, .str .x .x6 c.dataReg 0, ldS .x6 (c.buf + 1), .str .x .x6 c.dataReg 8,
   .subImm .x c.leftReg c.leftReg 1]

/-- The buffer's first block XORed into the next block of the data. -/
def encChain : List Instr :=
  [.ldr .x .x6 c.dataReg 16, ldS .x7 c.buf, eorR .x6 .x6 .x7, .str .x .x6 c.dataReg 16,
   .ldr .x .x6 c.dataReg 24, ldS .x7 (c.buf + 1), eorR .x6 .x6 .x7, .str .x .x6 c.dataReg 24]

/-- On to the next block. -/
def encNext : List Instr := [.addImm .x c.dataReg c.dataReg 16]

/-- One block: encrypted in the buffer, back to the data, and chained into
the next. -/
def cbcEncBlock : Prog isa :=
  .seq (.block c.encIn) (.seq c.crypt (.seq (.block c.encOut)
    (.seq (.ite (.zero .x c.leftReg) (.block []) (.block c.encChain)) (.block c.encNext))))

/-- The whole function: the IV into the first block, the key, then the
blocks. -/
def cbcEncrypt (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r)) (.seq (cbcWhiten r) (.seq (.block (c.ctrArgs r))
    (.seq c.prepare
      (.seq (.ite (.zero .x c.leftReg) (.block []) (.loop c.cbcEncBlock (.nonzero .x c.leftReg)))
        (.block c.restoreRegs)))))

end Core

end VG.Impl.Modes.AArch64
