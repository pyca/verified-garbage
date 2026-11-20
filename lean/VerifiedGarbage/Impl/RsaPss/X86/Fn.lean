module

public import VerifiedGarbage.Impl.RsaPss.X86.Table
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSASSA-PSS's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrub rb`, or
`Impl.Scrub.X86.scrubF rb W` for one with frames or calls: the `W` bytes of
stack below `esp` that it and its callees use zeroed), the registers a
callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.RsaPss.X86.Fn

open VG.X86

/-- `vg_rsa_pss_verify_precomputed`, with the hash functions `f` and MGF1's
`g` of its tables and calling the public-key operation `pubC` by its name
`pubN`, as emitted. -/
def verifyPrecomputed (f : Impl.RsaPss.X86.MdFns) (g : Impl.RsaOaep.X86.Fns) (pubN : String) (pubC : Prog isa) :
    Prog isa :=
  Impl.Scrub.X86.scrubF 32 260 (Impl.RsaPss.X86.verifyPrecomputed f g pubN pubC)

end VG.Impl.RsaPss.X86.Fn
