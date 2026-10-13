module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr

/-!
# SM4-CTR, bitsliced, on AArch64

`ctr(schedule = x0, ctr = x1, data = x2, n = x3, scratch = x4)`:
`vg_sm4_ctr`, the modes' generic CTR (`Impl/Modes/AArch64/Ctr.lean`) over
SM4's core, `modeCore`, with the working space in the scratch buffer
(`Layers.lean` has its layout), which the artifact allocates on the stack.

SM4's core is ECB's: `prepare` sets the masks and builds the table of
bitsliced round keys in encryption order (`dirCore .encrypt`), once; `crypt` transforms the
sixteen blocks of the tail buffer in place. Only the schedule's address
(`x0`) is a key argument; both keep `x1` and `x2`, where ECB keeps the
data's address and the blocks left too.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- SM4's core for the modes, its round keys in the order of the direction
`d`: encryption's for CTR and CBC encryption, decryption's for CBC
decryption. -/
def dirCore (d : Dir) : Impl.Modes.AArch64.Core where
  prepare := .seq (.block (setSlots keyMasks)) (keys d)
  crypt := .seq (.block (slotAddr .x3 tableEnd)) crypt16
  slots := tableEnd
  total := slots
  buf := tailSlot
  lgG := 4
  keyRegs := [.x0]
  dataReg := .x1
  leftReg := .x2

/-- SM4's core for encryption. -/
abbrev modeCore : Impl.Modes.AArch64.Core := dirCore .encrypt

/-- `vg_sm4_ctr`. -/
def ctr : Prog isa := modeCore.ctr ⟨.x1, .x2, .x3, .x4⟩

end VG.Impl.Sm4.AArch64
