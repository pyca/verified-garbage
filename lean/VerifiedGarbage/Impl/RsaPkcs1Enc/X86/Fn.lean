module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Random
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSAES-PKCS1-v1_5's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrub rb`, or
`Impl.Scrub.X86.scrubF rb W` for one with frames or calls: the `W` bytes of
stack below `esp` that it and its callees use zeroed), the registers a
callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86.Fn

open VG.X86

/-- `vg_rsa_pkcs1_encrypt_random`, calling the encryption `enc` by its name
`encName`, as emitted. -/
def encryptRandom (encName : String) (enc : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 2296 (Random.code encName enc)

end VG.Impl.RsaPkcs1Enc.X86.Fn
