module

public import VerifiedGarbage.Impl.Argon2.X86_64.Derive
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # Argon2 on x86-64: the function as emitted

`vg_argon2_derive` over an implementation of G (`Compressor`) and of
BLAKE2b's streaming functions (`hash`), then its cleanup
(`Impl.Scrub.X86_64.scrubAll v 0 344`): every vector register at the level
`v` and every caller-saved register cleared, and its 344 bytes of stack
wiped (the residue analysis does not follow its code).
-/

@[expose] public section

namespace VG.Impl.Argon2.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.Argon2.deriveApi`'s function as emitted, its cleanup at the level
`v`. -/
def derive [Compressor] (v : VecLevel) (name : String) (hash : HPrime.Hash) : Prog isa :=
  scrubAll v 0 344 (Impl.Argon2.X86_64.Derive.code name hash)

end VG.Impl.Argon2.X86_64.Fn
