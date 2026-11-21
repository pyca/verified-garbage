module

public import VerifiedGarbage.Impl.Scrypt.X86_64.Scrypt
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # scrypt on x86-64: the function as emitted

`vg_scrypt` over an implementation of ROMix and one of PBKDF2-HMAC-SHA256,
then its cleanup (`Impl.Scrub.X86_64.scrubAll v 0 88`): every vector
register at the level `v` and every caller-saved register cleared, and its
88 bytes of stack wiped (the residue analysis does not follow its code).
-/

@[expose] public section

namespace VG.Impl.Scrypt.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.Scrypt.scryptApi`'s function as emitted, over the ROMix `romix`
named `romixName` and the PBKDF2 `pbk` named `pbkName`, its cleanup at the
level `v`. -/
def scrypt (v : VecLevel) (romixName : String) (romix : Prog isa) (pbkName : String) (pbk : Prog isa) :
    Prog isa :=
  scrubAll v 0 88 (Impl.Scrypt.X86_64.scrypt romixName romix pbkName pbk)

end VG.Impl.Scrypt.X86_64.Fn
