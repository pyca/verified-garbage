module

public import VerifiedGarbage.Impl.Aes.X86_64.Callee
public import VerifiedGarbage.Impl.AesCtr.X86_64
public import VerifiedGarbage.Impl.AesCtr.X86_64.Final
public import VerifiedGarbage.Impl.StackScratch.X86_64

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AesCtr on x86-64: the functions as emitted

Each function, generic over the implementations it calls, then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`): every vector register at the level
`v` and every caller-saved register but the `rb` bits of the result
cleared, and the `n` bytes of stack its frames and calls use wiped.
-/

@[expose] public section

namespace VG.Impl.AesCtr.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.Ctr.aesApi`'s function as emitted, its cleanup at the level `v`. -/
def ctr (v : VecLevel) (callee : Impl.Aes.X86_64.Ctr32) : Prog isa :=
  scrubAll v 0 8 (Impl.AesCtr.X86_64.crypt callee)

/-- `Spec.Ctr.aesFinalApi`'s function as emitted, its cleanup at the level `v`. -/
def ctrFinal (v : VecLevel) (callee : Impl.Aes.X86_64.Ctr32) (suffix : String) : Prog isa :=
  scrubAll v 0 96 (Impl.StackScratch.X86_64.withStackArgScratch 80 0 (Impl.AesCtr.X86_64.cryptFinal callee suffix))

end VG.Impl.AesCtr.X86_64.Fn
