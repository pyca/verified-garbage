module

public import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr32
public import VerifiedGarbage.Impl.Modes.AArch64.CfbDec

/-!
# SM4's modes with the Armv8 SM4 instructions

`vg_sm4_ctr_sm4`, `vg_sm4_ctr32_sm4`, `vg_sm4_cbc_decrypt_chained_sm4` and
`vg_sm4_cfb128_decrypt_sm4`: the modes' generic code
(`Impl/Modes/AArch64/`) over a core that transforms eight blocks with
`sm4e` (`Ecb.lean`), for CPUs with FEAT_SM4.

The core prepares nothing: the schedule's address stays in `x0`, which no
mode writes. `crypt` loads the round keys from it, in the order the
direction's rounds use them, into `v16`–`v23`, the eight blocks of the
buffer (the scratch buffer's first sixteen words, at `sb`) into `v0`–`v7`,
runs the 32 rounds on each and stores them back. It writes no
general-purpose register. The scratch buffer is the core's buffer and the
modes' twelve words after it.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64.Sm4e

open VG.AArch64
open VG.Impl.Sm4.AArch64 (Dir)
open VG.Impl.Aes.AArch64 (sb)

/-- The round keys, then the eight blocks of the buffer transformed in place. -/
def cryptBuf (d : Dir) : List Instr :=
  dirKeys d ++ ldData sb regs8 0 ++ crypt regs8 ++ stData sb regs8 0

/-- SM4's core for the modes, its round keys in the order of the direction
`d`. -/
def core (d : Dir) : Impl.Modes.AArch64.Core where
  prepare := .block []
  crypt := .block (cryptBuf d)
  slots := 16
  total := 28
  buf := 0
  lgG := 3
  keyRegs := [.x0]
  dataReg := .x23
  leftReg := .x24

/-- `vg_sm4_ctr_sm4`. -/
def ctr : Prog isa := (core .encrypt).ctr ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_sm4_ctr32_sm4`. -/
def ctr32 : Prog isa := (core .encrypt).ctr32 ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_sm4_cbc_decrypt_chained_sm4`. -/
def cbcDecryptChained : Prog isa := (core .decrypt).cbcDecryptChained ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_sm4_cfb128_decrypt_sm4`. -/
def cfbDecrypt : Prog isa := (core .encrypt).cfbDecryptBatched ⟨.x1, .x2, .x3, .x4⟩

end VG.Impl.Sm4.AArch64.Sm4e
