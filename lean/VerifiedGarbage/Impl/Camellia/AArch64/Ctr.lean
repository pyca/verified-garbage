module

public import VerifiedGarbage.Impl.Camellia.AArch64.Ecb
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr

/-!
# Camellia-CTR, bitsliced, on AArch64

`ctr(schedule = x0, rounds = x1, ctr = x2, data = x3, n = x4, scratch = x5)`:
`vg_camellia_ctr`, the modes' generic CTR (`Impl/Modes/AArch64/Ctr.lean`)
over Camellia's core, `modeCore`, with the working space in the scratch
buffer (`Layers.lean` has its layout), which the artifact allocates on the
stack.

Camellia's core is ECB's: `prepare` sets the masks and builds the table of
bitsliced subkeys for 18 or 24 rounds in encryption order (`dirCore
.encrypt`), once, leaving
the address of its postwhitening entry in `x4`; `crypt` is `crypt8`, which
transforms the eight blocks of the tail buffer and keeps the data's address
(`x2`), the blocks left (`x3`) and that address, as in ECB. The schedule's
address (`x0`) and the number of rounds (`x1`) are the key arguments.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- Camellia's core for the modes, its subkeys in the order of the direction
`d`: encryption's for CTR and CBC encryption, decryption's for CBC
decryption. -/
def dirCore (d : Dir) : Impl.Modes.AArch64.Core where
  prepare := .seq (.block (setSlots layerMasks ++ ([.subImm .x t0 .x1 18] : List Instr)))
    (.ite (.zero .x t0) (keys d 3) (keys d 4))
  crypt := crypt8
  slots := tailSlot + 16
  total := slots
  buf := tailSlot
  lgG := 3
  keyRegs := [.x0, .x1]
  dataReg := .x2
  leftReg := .x3

/-- Camellia's core for encryption. -/
abbrev modeCore : Impl.Modes.AArch64.Core := dirCore .encrypt

/-- `vg_camellia_ctr`. -/
def ctr : Prog isa := modeCore.ctr ⟨.x2, .x3, .x4, .x5⟩

end VG.Impl.Camellia.AArch64
