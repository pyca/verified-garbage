module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Sign
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed

/-! # RSASSA-PKCS1-v1_5 on x86-64: the functions as emitted

Each function over the implementations it calls, then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`) at the level `v` of the vector
instructions of its code and theirs: every vector register at that level and
every caller-saved register but the `rb` bits of the result cleared, and the
`n` bytes of stack its frames and calls use zeroed.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.RsaPkcs1Sig.signPrecomputedApi`'s function as emitted, over the
checked private operation `priv` named `privName`. -/
def signPrecomputed (v : VecLevel) (privName : String) (priv : Prog isa) : Prog isa :=
  scrubAll v 32 4456 (Sign.codeP privName priv)

/-- `Spec.RsaPkcs1Sig.verifyPrecomputedApi`'s function as emitted, over the
public operation `pub` named `pubName`. -/
def verifyPrecomputed (v : VecLevel) (pubName : String) (pub : Prog isa) : Prog isa :=
  scrubAll v 32 2144 (Precomputed.code pubName pub)

/-- `Spec.RsaPkcs1Sig.recoverPrecomputedApi`'s function as emitted, over the
public operation `pub` named `pubName`. -/
def recoverPrecomputed (v : VecLevel) (pubName : String) (pub : Prog isa) : Prog isa :=
  scrubAll v 32 2144 (RecoverPrecomputed.code pubName pub)

end VG.Impl.RsaPkcs1Sig.X86_64.Fn
