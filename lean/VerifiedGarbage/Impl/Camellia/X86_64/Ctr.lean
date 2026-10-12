module

public import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr

/-!
# Camellia-CTR, bitsliced, on x86-64

`ctr(schedule = rdi, rounds = rsi, ctr = rdx, data = rcx, n = r8, scratch = r9)`:
`vg_camellia_ctr`, the modes' generic CTR (`Impl/Modes/X86_64/Ctr.lean`)
over Camellia's core, `modeCore`, with the working space in the scratch
buffer (`Layers.lean` has its layout), which the artifact allocates on the
stack.

Camellia's core is ECB's: `prepare` sets the masks and builds the table of
bitsliced subkeys for 18 or 24 rounds in encryption order, once, leaving
the address of its postwhitening entry in `rdi`; `crypt` transforms the
eight blocks of the tail buffer, keeping the data's address (`rdx`), the
blocks left (`r8`) and that address in their slots while `crypt8` runs, as
ECB does (`saveState`, `loadState`). The schedule's address (`rdi`) and the
number of rounds (`rsi`) are the key arguments.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- Camellia's core for the modes, its subkeys in the order of the direction
`d`: encryption's for CTR, decryption's for CBC decryption. -/
def dirCore (d : Dir) : Impl.Modes.X86_64.Core where
  prepare := .seq (.block (setMasks layerMasks ++ ([.alu .cmp .rsi (.imm 18)] : List Instr)))
    (.ite .e (keys d 3) (keys d 4))
  crypt := .seq (.block saveState) (.seq crypt8 (.block loadState))
  slots := tailSlot + 16
  total := slots
  buf := tailSlot
  G := 8
  keyRegs := [.rdi, .rsi]
  dataReg := .rdx
  leftReg := .r8

/-- Camellia's core for encryption. -/
abbrev modeCore : Impl.Modes.X86_64.Core := dirCore .encrypt

/-- `vg_camellia_ctr`. -/
def ctr : Prog isa := modeCore.ctr ⟨.rdx, .rcx, .r8, .r9⟩

end VG.Impl.Camellia.X86_64
