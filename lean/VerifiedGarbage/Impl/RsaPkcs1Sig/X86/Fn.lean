module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSASSA-PKCS1-v1_5's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`): the `W`
bytes of stack below `esp` that it and its callees use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.X86.Fn

open VG.X86

/-- `vg_rsa_pkcs1_sign_precomputed`, calling the private-key operation
`priv` by its name `privN`, as emitted. -/
def signPrecomputed (privN : String) (priv : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 4584 (Sign.code privN priv Sign.callArgsP)

end VG.Impl.RsaPkcs1Sig.X86.Fn
