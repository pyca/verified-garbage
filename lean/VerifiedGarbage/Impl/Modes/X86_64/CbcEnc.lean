import VerifiedGarbage.Impl.Modes.X86_64.Ctr

/-!
# CBC encryption on x86-64, for any block cipher with blocks of 8 or 16 bytes

`cbcEncrypt core regs`: CBC encryption (SP 800-38A §6.2) over a block
cipher's core (`Core`, as for CTR), whose `crypt` applies the forward cipher
`CIPH_K` to the `G` blocks of its buffer. Encryption is sequential: each
block's input is the previous block's output, so each call of `crypt`
encrypts one block, in the buffer's first, and the other `G - 1` are wasted.

The chaining value is never held apart from the data: the IV, which is only
read, is XORed into the first block at entry, and after block `j` is
encrypted in place its ciphertext `Cⱼ` is XORed into block `j + 1`. Each
block of the data is thus `Pⱼ ⊕ Cⱼ₋₁` when its turn comes, and only the
data's address and the blocks left, in `dataReg` and `leftReg`, are carried
across `crypt`.

Only the pointers and `n` (and what is computed from them) are public; no
address or branch depends on the key, the IV or the data.
-/

namespace VG.Impl.Modes.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

namespace Core

variable (c : Core)

/-- The IV at `r.ctr` XORed into the first block at `r.data`, unless `r.n`
is zero. -/
def cbcWhiten (r : CtrRegs) : Prog isa :=
  .seq (.block [.alu .test r.n (.reg r.n)])
    (.ite .e (.block [])
      (.block ((List.range c.bw).flatMap (xorW .rax r.data r.ctr 0 0))))

/-- The block at `dataReg` to the buffer's first. -/
def encIn : List Instr :=
  (List.range c.bw).flatMap (copyW .rax sb c.dataReg (8 * c.buf) 0)

/-- The buffer's first block back to `dataReg`, and one block fewer left
(ZF set when none is). -/
def encOut : List Instr :=
  (List.range c.bw).flatMap (copyW .rax c.dataReg sb 0 (8 * c.buf)) ++
    ([.alu .sub c.leftReg (.imm 1)] : List Instr)

/-- The buffer's first block XORed into the next block of the data. -/
def encChain : List Instr :=
  (List.range c.bw).flatMap (xorW .rax c.dataReg sb (8 * c.bw) (8 * c.buf))

/-- On to the next block; ZF is set when none is left. -/
def encNext : List Instr :=
  [.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw))), .alu .test c.leftReg (.reg c.leftReg)]

/-- One block: encrypted in the buffer, back to the data, and chained into
the next. -/
def cbcEncBlock : Prog isa :=
  .seq (.block c.encIn) (.seq c.crypt (.seq (.block c.encOut)
    (.seq (.ite .e (.block []) (.block c.encChain)) (.block c.encNext))))

/-- The whole function: the IV into the first block, the key, then the
blocks. -/
def cbcEncrypt (r : CtrRegs) : Prog isa :=
  .seq (.block (c.ctrEntry r)) (.seq (c.cbcWhiten r) (.seq (.block (c.ctrArgs r))
    (.seq c.prepare
      (.seq (.block [.alu .test c.leftReg (.reg c.leftReg)])
        (.seq (.ite .e (.block []) (.loop c.cbcEncBlock .ne)) (.block c.restoreRegs))))))

end Core

end VG.Impl.Modes.X86_64
