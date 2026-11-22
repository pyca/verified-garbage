module

public import VerifiedGarbage.Impl.Sm4.X86.AesNiWide
public import VerifiedGarbage.Impl.StackScratch.X86

/-! # SM4's counter mode with GCM's `inc₃₂` by the AES S-box on x86 (32-bit) -/

@[expose] public section

namespace VG.Impl.Sm4.X86.AesNiWide

open VG.X86

/-- `vg_sm4_ctr32`: CTR (`AesNiWide.ctr`) with GCM's `inc₃₂` on the counter
block's last 32 bits, with its scratch buffer as the fifth argument. -/
def ctr32 : Prog isa := (core .encrypt).seqLevels Modes.Mode.ctr32Wide levels Modes.Mode.ctr32Early

/-- `ctr32` with its working space on the stack: the internal function
`vg_sm4_ctr32_aesni`, which SM4-GCM's functions call. -/
def ctr32Framed : Prog isa := Impl.StackScratch.X86.withStackScratchWiped 752 4 182 ctr32

end VG.Impl.Sm4.X86.AesNiWide
