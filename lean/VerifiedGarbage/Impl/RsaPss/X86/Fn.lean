module

public import VerifiedGarbage.Impl.RsaPss.X86.Table
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSASSA-PSS's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`): the `W`
bytes of stack below `esp` that it and its callees use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.RsaPss.X86.Fn

open VG.X86

/-- `vg_rsa_pss_sign_precomputed`, with the hash functions `f` and MGF1's
`g` of its tables and calling the private-key operation `priv` by its name
`privN`, as emitted. -/
def signPrecomputed (f : Impl.RsaPss.X86.MdFns) (g : Impl.RsaOaep.X86.Fns) (privN : String) (priv : Prog isa) :
    Prog isa :=
  Impl.Scrub.X86.scrubF 32 3608 (Impl.RsaPss.X86.sign f g privN priv Impl.RsaPss.X86.privArgsP)

end VG.Impl.RsaPss.X86.Fn
