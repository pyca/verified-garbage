import VerifiedGarbage.Impl.TripleDes.AArch64.Block
import VerifiedGarbage.Impl.Modes.AArch64.Cbc
import VerifiedGarbage.Impl.Modes.AArch64.CbcEnc

/-!
# Triple DES-CBC on AArch64

`cbcEncrypt` and `cbcDecrypt` (schedule = x0, iv = x1, data = x2, n = x3,
scratch = x4): the modes' generic CBC (`Impl/Modes/AArch64/Cbc.lean`,
`CbcEnc.lean`) over the scalar block function (`block`), one 8-byte block at
a time, with the working space in the scratch buffer, which the artifact
allocates on the stack.

The core's slots: the block function's 64 (`x2`), the buffer's one block,
and a copy of the 384-byte schedule, which `prepare` makes so that nothing
the modes write can reach it. `crypt` points `x0`, `x1` and `x2` at the
copy, the buffer and the block function's slots, and restores the scratch
buffer's address (`sb`, which the block function overwrites) from `x2`.
The block function keeps `x23` and `x24`, which carry the data's address
and the blocks left.
-/

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

/-- Triple DES's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Impl.Modes.AArch64.Core where
  prepare := .block ((List.range 48).flatMap (copyW .x6 sb .x0 (8 * schedSlot) 0))
  crypt := .seq (.block [.addImm .x .x0 sb (8 * schedSlot), .addImm .x .x1 sb (8 * cbcBuf), rr .x2 sb])
    (.seq (dirBlock d) (.block [rr sb .x2]))
  slots := schedSlot + 48
  total := schedSlot + 60
  buf := cbcBuf
  lgG := 0
  bw := 1
  keyRegs := [.x0]
  dataReg := .x23
  leftReg := .x24

/-- `vg_triple_des_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := (dirCore .encrypt).cbcEncrypt ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_triple_des_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := (dirCore .decrypt).cbcDecrypt ⟨.x1, .x2, .x3, .x4⟩

end VG.Impl.TripleDes.AArch64
