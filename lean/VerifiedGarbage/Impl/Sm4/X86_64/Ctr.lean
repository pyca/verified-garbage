module

public import VerifiedGarbage.Impl.Sm4.X86_64.Prepared
public import VerifiedGarbage.Impl.Modes.X86_64.Ctr

/-!
# SM4-CTR, bitsliced, on x86-64

`ctr(schedule = rdi, ctr = rsi, data = rdx, n = rcx, scratch = r8)`:
`vg_sm4_ctr`, the modes' generic CTR (`Impl/Modes/X86_64/Ctr.lean`) over
SM4's core, `modeCore`, with the working space in the scratch buffer
(`Layers.lean` has its layout), which the artifact allocates on the stack.

SM4's core is ECB's: `prepare` sets the masks and builds the table of
bitsliced round keys in encryption order (`dirCore .encrypt`), once, inline;
`crypt` calls `vg_sm4_crypt_prepared` (`Prepared.lean`), which transforms
the sixteen blocks of the tail buffer in place. The core's slots are ECB's
392, the modes' 8 after them, and the call's return address is the stack it
uses. The key arguments are the schedule's address (`rdi`) and `rsp`, below
which the call's stack is apart from the slots. Both keep `rdx` and `r8`,
where ECB keeps the data's address and the blocks left too, and which
`vg_sm4_crypt_prepared` does not write.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- SM4's core for the modes, its round keys in the order of the direction
`d`: encryption's for CTR, decryption's for CBC decryption. -/
def dirCore (d : Dir) : Impl.Modes.X86_64.Core where
  prepare := .seq (.block (setMasks keyMasks)) (keys d)
  crypt := cryptCall
  slots := slots
  total := slots + 8
  buf := tailSlot
  G := 16
  keyRegs := [.rdi, .rsp]
  dataReg := .rdx
  leftReg := .r8
  stack := 8

/-- SM4's core for encryption. -/
abbrev modeCore : Impl.Modes.X86_64.Core := dirCore .encrypt

/-- `vg_sm4_ctr`. -/
def ctr : Prog isa := modeCore.ctr ⟨.rsi, .rdx, .rcx, .r8⟩

end VG.Impl.Sm4.X86_64
