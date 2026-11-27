module

public import VerifiedGarbage.Impl.Aes.X86_64.Callee
public import VerifiedGarbage.Impl.AesCfb8.X86_64

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AesCfb8 on x86-64: the functions as emitted

Each function, generic over the implementations it calls, then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`): every vector register at the level
`v` and every caller-saved register but the `rb` bits of the result
cleared, and the `n` bytes of stack its frames and calls use wiped.
-/

@[expose] public section

namespace VG.Impl.AesCfb8.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.Cfb8.aesEncryptApi`'s function as emitted, its cleanup at the level `v`. -/
def cfb8Encrypt (v : VecLevel) (enc : Impl.Aes.X86_64.Blocks) : Prog isa :=
  scrubAll v 0 8 (Impl.AesCfb8.X86_64.encrypt enc)

/-- `Spec.Cfb8.aesDecryptApi`'s function as emitted, its cleanup at the level `v`. -/
def cfb8Decrypt (v : VecLevel) (enc : Impl.Aes.X86_64.Blocks) : Prog isa :=
  scrubAll v 0 8 (Impl.AesCfb8.X86_64.decrypt enc)

end VG.Impl.AesCfb8.X86_64.Fn
