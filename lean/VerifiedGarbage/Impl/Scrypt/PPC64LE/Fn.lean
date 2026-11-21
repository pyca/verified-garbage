module

public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Scrypt
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# scrypt on PPC64LE: the function as emitted

`vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256 named
`pbkName`, followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): it returns
nothing, and the cleanup zeroes the 1120 bytes of stack its frames and those
of the functions it calls use, and clears the volatile registers it writes,
the vector registers of SHA-256's compression function among them, so that
it returns without secret residue (`Proof/Scrypt/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Scrypt.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_scrypt`, calling `pbk` (named `pbkName`), as emitted. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  scrubAll 0 1120 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.Scrypt.PPC64LE.Whole.scrypt pbkName pbk)

end VG.Impl.Scrypt.PPC64LE.Fn
