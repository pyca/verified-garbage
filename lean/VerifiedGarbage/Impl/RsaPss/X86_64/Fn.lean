module

public import VerifiedGarbage.Impl.Scrub.X86_64.FnUp
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding

/-! # RSASSA-PSS on x86-64: the functions as emitted

Each function over the tables of the hash functions it calls and the
implementation of the RSA operation, then its cleanup
(`Impl.Scrub.X86_64.scrubAllOrUp v rb n`), as RSAES-OAEP's
(`Impl/RsaOaep/X86_64/Fn.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaPss.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAllOrUp)

/-- `Spec.RsaPss.signPrecomputedMdTableApi`'s function as emitted, over the
hash functions `f` and `g` and the checked private operation `privC` named
`privN`. -/
def signPrecomputed (v : VecLevel) (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) (privN : String)
    (privC : Prog isa) : Prog isa :=
  scrubAllOrUp v 32 3656 (signCP f g privN privC)

/-- `Spec.RsaPss.verifyPrecomputedMdTableApi`'s function as emitted, over the
hash functions `f` and `g` and the public operation `pubC` named `pubN`. -/
def verifyPrecomputed (v : VecLevel) (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) (pubN : String)
    (pubC : Prog isa) : Prog isa :=
  scrubAllOrUp v 32 808 (verifyC f g pubN pubC)

end VG.Impl.RsaPss.X86_64.Fn
