module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyInit
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSA key generation's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrub rb`, or
`Impl.Scrub.X86.scrubF rb W` for one with frames or calls: the `W` bytes of
stack below `esp` that it and its callees use zeroed), the registers a
callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86.Fn

open VG.X86

/-- `vg_rsa_generate_init`, as emitted. -/
def generateInit : Prog isa := Impl.Scrub.X86.scrub 32 KeyInit.init

end VG.Impl.RsaKeyGen.X86.Fn
