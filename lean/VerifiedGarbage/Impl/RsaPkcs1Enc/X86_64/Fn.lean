module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Random

/-! # RSAES-PKCS1-v1_5 on x86-64: the functions as emitted

Each function over the implementations it calls, then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`) at the level `v` of the vector
instructions of its code and theirs: every vector register at that level and
every caller-saved register but the `rb` bits of the result cleared, and the
`n` bytes of stack its frames and calls use zeroed.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.RsaPkcs1Enc.encryptRandomApi`'s function as emitted, over the
encryption `enc` named `encName`. -/
def encryptRandom (v : VecLevel) (encName : String) (enc : Prog isa) : Prog isa :=
  scrubAll v 32 2288 (Random.code encName enc)

end VG.Impl.RsaPkcs1Enc.X86_64.Fn
