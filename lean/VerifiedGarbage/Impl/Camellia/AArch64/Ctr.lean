module

public import VerifiedGarbage.Impl.Camellia.AArch64.Prepared
public import VerifiedGarbage.Impl.Modes.AArch64.Ctr
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# Camellia-CTR, bitsliced, on AArch64

`ctr(schedule = x0, rounds = x1, ctr = x2, data = x3, n = x4, scratch = x5)`:
`vg_camellia_ctr`, the modes' generic CTR (`Impl/Modes/AArch64/Ctr.lean`)
over Camellia's core, `modeCore`, with the working space in the scratch
buffer (`Layers.lean` has its layout), which the artifact allocates on the
stack.

Camellia's core calls ECB's two halves (`Prepared.lean`): `prepare` calls
`vg_camellia_prepare_keys`, which sets the masks and builds the table of
bitsliced subkeys for 18 or 24 rounds in the order of the direction
(`dirCore .encrypt` for encryption), once, and keeps the number of rounds
in `x4`; `crypt` calls `vg_camellia_crypt_prepared`, which transforms the
eight blocks of the tail buffer in place. The schedule's address (`x0`)
and the number of rounds (`x1`) are the key arguments. The modes keep the
data's address and the blocks left in `x23` and `x24`, which the calls
keep in vector registers, with the return address, `sb` and `x4`. The
core's slots are the functions' 406, the modes' 12 after them.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- Camellia's core for the modes, its subkeys in the order of the direction
`d`: encryption's for CTR and CBC encryption, decryption's for CBC
decryption. -/
def dirCore (d : Dir) : Impl.Modes.AArch64.Core where
  prepare := prepareCall d
  crypt := cryptCall
  slots := slots
  total := slots + 12
  buf := tailSlot
  lgG := 3
  keyRegs := [.x0, .x1]
  dataReg := .x23
  leftReg := .x24

/-- Camellia's core for encryption. -/
abbrev modeCore : Impl.Modes.AArch64.Core := dirCore .encrypt

/-- `vg_camellia_ctr`. -/
def ctr : Prog isa := modeCore.ctr ⟨.x2, .x3, .x4, .x5⟩

end VG.Impl.Camellia.AArch64

namespace VG.Impl.Camellia.AArch64.Fn

open VG.AArch64

/-- Camellia-CTR as emitted: its code with its scratch space on the stack
(`Impl.StackScratch.AArch64.withStackScratch`), then the registers it writes
that the calling convention does not preserve cleared and its 3344 bytes of
stack zeroed (`Impl.Scrub.AArch64.scrubAll`), so that it returns without
secret residue. -/
def ctr : Prog isa :=
  VG.Impl.Scrub.AArch64.scrubAll 3344 0
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v26, .v27, .v28, .v29, .v30],
     []⟩
    (VG.Impl.StackScratch.AArch64.withStackScratch 3344 .x5 VG.Impl.Camellia.AArch64.ctr)

end VG.Impl.Camellia.AArch64.Fn
