module

public import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr32
public import VerifiedGarbage.Impl.Modes.AArch64.CfbDec
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal

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

`vg_sm4_cbc_encrypt_chained_sm4`, `vg_sm4_ofb_sm4`,
`vg_sm4_cfb128_encrypt_sm4`, and the functions of a message's last piece,
`vg_sm4_ofb_final_sm4`, `vg_sm4_cfb128_encrypt_final_sm4` and
`vg_sm4_cfb128_decrypt_final_sm4`: the modes whose blocks each depend on
the one before, over a core of one block (`core1`), the same code with the
buffer's one block in `v0`. Its scratch buffer is fourteen words. It writes
no general-purpose register either, so the IV's address stays in `x19`,
where these modes keep it.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64.Sm4e

open VG.AArch64
open VG.Impl.Sm4.AArch64 (Dir)
open VG.Impl.Aes.AArch64 (sb)

/-- The round keys, then the blocks of the buffer, one for each register
of `regs`, transformed in place. -/
def cryptBuf (regs : List VReg) (d : Dir) : List Instr :=
  dirKeys d ++ ldData sb regs 0 ++ crypt regs ++ stData sb regs 0

/-- SM4's core for the modes, of the `2 ^ lg` blocks in `regs`, its round
keys in the order of the direction `d`: the scratch buffer is the blocks,
then the modes' twelve words. -/
def coreOf (regs : List VReg) (lg : Nat) (d : Dir) : Impl.Modes.AArch64.Core where
  prepare := .block []
  crypt := .block (cryptBuf regs d)
  slots := 2 * regs.length
  total := 2 * regs.length + 12
  buf := 0
  lgG := lg
  keyRegs := [.x0]
  dataReg := .x23
  leftReg := .x24

/-- SM4's core of eight blocks. -/
def core (d : Dir) : Impl.Modes.AArch64.Core := coreOf regs8 3 d

/-- SM4's core of one block, for the modes that chain their blocks. -/
def core1 (d : Dir) : Impl.Modes.AArch64.Core := coreOf [.v0] 0 d

/-- `vg_sm4_ctr_sm4`. -/
def ctr : Prog isa := (core .encrypt).ctr ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_sm4_ctr32_sm4`. -/
def ctr32 : Prog isa := (core .encrypt).ctr32 ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_sm4_cbc_decrypt_chained_sm4`. -/
def cbcDecryptChained : Prog isa := (core .decrypt).cbcDecryptChained ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_sm4_cfb128_decrypt_sm4`. -/
def cfbDecrypt : Prog isa := (core .encrypt).cfbDecryptBatched ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_sm4_cbc_encrypt_chained_sm4`. -/
def cbcEncryptChained : Prog isa := (core1 .encrypt).cbcEncryptChained ⟨.x1, .x2, .x3, .x4⟩ .x19

/-- `vg_sm4_ofb_sm4`, `vg_sm4_cfb128_encrypt_sm4`. -/
def fb (m : Impl.Modes.FbMode) : Prog isa := (core1 .encrypt).fb m ⟨.x1, .x2, .x3, .x4⟩ .x19

/-- `vg_sm4_ofb_final_sm4`, `vg_sm4_cfb128_encrypt_final_sm4`,
`vg_sm4_cfb128_decrypt_final_sm4`. -/
def fbFinal (m : Impl.Modes.FbMode) : Prog isa := (core1 .encrypt).fbFinal m ⟨.x1, .x2, .x3, .x4⟩ .x19

end VG.Impl.Sm4.AArch64.Sm4e
