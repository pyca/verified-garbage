module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.RsaOaep.X86_64
public import VerifiedGarbage.Impl.RsaOaep.X86_64.Precomputed

/-! # RSAES-OAEP on x86-64: the functions as emitted

Each function over the tables of the hash functions it calls and the
implementation of the RSA operation, then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`): at the level `sse` of an
implementation without vector instructions, every SSE register cleared
(the AVX hash functions it runs through its tables end with `vzeroupper`),
and at a higher level `v`, every vector register at that level; every
caller-saved register but the `rb` bits of the result cleared, and the `n`
bytes of stack its frames and calls use zeroed.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.Mgf1.X86_64.Table (Fns)

/-- `Spec.RsaOaep.decryptPrecomputedMdTablesApi`'s function as emitted,
over the hash functions `f` and the checked private operation `privC` named
`privN`. -/
def decryptPrecomputed (v : VecLevel) (f : Fns) (privN : String) (privC : Prog isa) : Prog isa :=
  scrubAll v 32 3560 (decryptP f privN privC)

/-- `Spec.RsaOaep.encryptMdTablesApi`'s function as emitted, over the hash
functions `f` and the public operation `pubC` named `pubN`. -/
def encrypt (v : VecLevel) (f : Fns) (pubN : String) (pubC : Prog isa) : Prog isa :=
  scrubAll v 32 312 (Precomputed.encrypt f pubN pubC)

end VG.Impl.RsaOaep.X86_64.Fn
