module

public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.AesOfb.X86_64.Final
public import VerifiedGarbage.Impl.Aes.X86_64.Callee
public import VerifiedGarbage.Impl.AesOfb.X86_64

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AesOfb on x86-64: the functions as emitted

Each function, generic over the implementations it calls, then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`): every vector register at the level
`v` and every caller-saved register but the `rb` bits of the result
cleared, and the `n` bytes of stack its frames and calls use wiped.
-/

@[expose] public section

namespace VG.Impl.AesOfb.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.Ofb.aesApi`'s function as emitted, its cleanup at the level `v`. -/
def ofb (v : VecLevel) (enc : Impl.Aes.X86_64.Blocks) : Prog isa :=
  scrubAll v 0 8 (Impl.AesOfb.X86_64.crypt enc)

/-- `Spec.Ofb.aesFinalApi`'s function as emitted, its cleanup at the level `v`. -/
def ofbFinal (v : VecLevel) (enc : Impl.Aes.X86_64.Blocks) (suffix : String) : Prog isa :=
  scrubAll v 0 80 (Impl.StackScratch.X86_64.withStackArgScratch 64 0 (Impl.AesOfb.X86_64.cryptFinal enc suffix))

end VG.Impl.AesOfb.X86_64.Fn
