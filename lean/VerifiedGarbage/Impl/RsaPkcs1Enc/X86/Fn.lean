module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RSAES-PKCS1-v1_5's functions on x86 (32-bit), as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`): the `W`
bytes of stack below `esp` that it and its callees use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86.Fn

open VG.X86

/-- `vg_rsa_pkcs1_decrypt_precomputed`, with SHA-256's functions `F` and
calling the private-key operation `priv` by its name `privN`, as emitted. -/
def decryptPrecomputed (F : Impl.Pbkdf2.Whole.X86.Fns) (privN : String) (priv : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 3568 (Decrypt.code F privN priv Decrypt.privArgsP)

end VG.Impl.RsaPkcs1Enc.X86.Fn
