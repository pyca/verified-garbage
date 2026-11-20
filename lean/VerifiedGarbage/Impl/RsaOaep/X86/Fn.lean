module

public import VerifiedGarbage.Impl.RsaOaep.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSAES-OAEP's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrub rb`, or
`Impl.Scrub.X86.scrubF rb W` for one with frames or calls: the `W` bytes of
stack below `esp` that it and its callees use zeroed), the registers a
callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.RsaOaep.X86.Fn

open VG.X86

/-- `vg_rsa_oaep_encrypt_precomputed`, with the hash functions `f` of its
tables and calling the public-key operation `pubC` by its name `pubN`, as
emitted. -/
def encryptPrecomputed (f : Impl.RsaOaep.X86.Fns) (pubN : String) (pubC : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 260 (Impl.RsaOaep.X86.encryptPrecomputed f pubN pubC)

/-- `vg_rsa_oaep_decrypt_precomputed`, with the hash functions `f` of its
tables and calling the private-key operation `priv` by its name `privN`, as
emitted. -/
def decryptPrecomputed (f : Impl.RsaOaep.X86.Fns) (privN : String) (priv : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 3608 (Impl.RsaOaep.X86.decrypt f privN priv Impl.RsaOaep.X86.privArgsP)

end VG.Impl.RsaOaep.X86.Fn
