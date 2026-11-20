module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Verify
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSASSA-PKCS1-v1_5's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrub rb`, or
`Impl.Scrub.X86.scrubF rb W` for one with frames or calls: the `W` bytes of
stack below `esp` that it and its callees use zeroed), the registers a
callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.X86.Fn

open VG.X86

/-- `vg_rsa_pkcs1_verify_precomputed`, calling the public-key operation
`pub` by its name `pubName`, as emitted. -/
def verifyPrecomputed (pubName : String) (pub : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 2228 (Verify.code pubName pub)

/-- `vg_rsa_pkcs1_recover_precomputed`, calling the public-key operation
`pub` by its name `pubName`, as emitted. -/
def recoverPrecomputed (pubName : String) (pub : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 2228 (Recover.code pubName pub)

end VG.Impl.RsaPkcs1Sig.X86.Fn
