module

public import VerifiedGarbage.Impl.Camellia.X86_64.Prepared
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr

/-!
# Camellia-CTR, bitsliced, on x86-64

`ctr(schedule = rdi, rounds = rsi, ctr = rdx, data = rcx, n = r8, scratch = r9)`:
`vg_camellia_ctr`, the modes' generic CTR (`Impl/Modes/X86_64/Ctr.lean`)
over Camellia's core, `modeCore`, with the working space in the scratch
buffer (`Layers.lean` has its layout), which the artifact allocates on the
stack.

Camellia's core is ECB's: `prepare` sets the masks and builds the table of
bitsliced subkeys for 18 or 24 rounds in encryption order, once, inline,
and leaves the number of rounds in `rdi`; `crypt` calls
`vg_camellia_crypt_prepared` (`Prepared.lean`), which transforms the eight
blocks of the tail buffer, keeping the data's address (`rdx`), the blocks
left (`r8`) and the number of rounds in callee-saved registers across the
call, and leaves the working space's address in `sb`. The core's slots are ECB's 401, the modes' 8 after them, and the
call's return address is the stack it uses. The key arguments are the
schedule's address (`rdi`), the number of rounds (`rsi`) and `rsp`, below
which the call's stack is apart from the slots.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- Camellia's core for the modes, its subkeys in the order of the direction
`d`: encryption's for CTR, decryption's for CBC decryption. -/
def dirCore (d : Dir) : Impl.Modes.X86_64.Core where
  prepare := .seq (.block (setMasks layerMasks ++ ([.alu .cmp .rsi (.imm 18)] : List Instr)))
    (.ite .e (.seq (keys d 3) (.block [.movImm64 .rdi 18])) (.seq (keys d 4) (.block [.movImm64 .rdi 24])))
  crypt := cryptCall
  slots := slots
  total := slots + 8
  buf := tailSlot
  G := 8
  keyRegs := [.rdi, .rsi, .rsp]
  dataReg := .rdx
  leftReg := .r8
  stack := 8

/-- Camellia's core for encryption. -/
abbrev modeCore : Impl.Modes.X86_64.Core := dirCore .encrypt

/-- `vg_camellia_ctr`. -/
def ctr : Prog isa := modeCore.ctr ⟨.rdx, .rcx, .r8, .r9⟩

end VG.Impl.Camellia.X86_64
