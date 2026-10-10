import VerifiedGarbage.Impl.TripleDes.X86_64.Block
import VerifiedGarbage.Impl.Modes.X86_64.Cbc
import VerifiedGarbage.Impl.Modes.X86_64.CbcEnc

/-!
# Triple DES-CBC on x86-64

`cbcEncrypt` and `cbcDecrypt` (schedule = rdi, iv = rsi, data = rdx,
n = rcx, scratch = r8): the modes' generic CBC (`Impl/Modes/X86_64/Cbc.lean`,
`CbcEnc.lean`) over the scalar block function (`block`), one 8-byte block at
a time, with the working space in the scratch buffer, which the artifact
allocates on the stack.

The core's slots: the block function's 64 (`rdx`), the buffer's one block,
and a copy of the 384-byte schedule, which `prepare` makes so that nothing
the modes write can reach it. `crypt` points `rdi`, `rsi` and `rdx` at the
copy, the buffer and the block function's slots, and restores the scratch
buffer's address (`sb`, which the block function uses) from `rdx`. The block
function keeps `r12` and `r13`, which carry the data's address and the
blocks left.
-/

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Impl.Modes.X86_64 (copyW)
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
def dirCore (d : Direction) : Impl.Modes.X86_64.Core where
  prepare := .block ((List.range 48).flatMap (copyW .rax sb .rdi (8 * schedSlot) 0))
  crypt := .seq (.block [movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot))), movR .rsi sb,
      .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * cbcBuf))), movR .rdx sb])
    (.seq (dirBlock d) (.block [movR sb .rdx]))
  slots := schedSlot + 48
  total := schedSlot + 56
  buf := cbcBuf
  G := 1
  bw := 1
  keyRegs := [.rdi]
  dataReg := .r12
  leftReg := .r13

/-- `vg_triple_des_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := (dirCore .encrypt).cbcEncrypt ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_triple_des_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := (dirCore .decrypt).cbcDecrypt ⟨.rsi, .rdx, .rcx, .r8⟩

end VG.Impl.TripleDes.X86_64
