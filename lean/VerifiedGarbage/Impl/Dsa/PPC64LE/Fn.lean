module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.PPC64LE.RandomSign
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# Dsa on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Dsa/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_dsa_derive_key`, as emitted. -/
def deriveKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.Derive.derive)

/-- `vg_dsa_sign_random_prevalidated`, as emitted. -/
def randomSignPrevalidated : Prog isa :=
  scrubAll 32 304 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.RandomSign.code)

/-- `vg_dsa_generate_key`, as emitted. -/
def generateKey : Prog isa :=
  scrubAll 32 304 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.Generate.code)

/-- `vg_dsa_validate_public_key`, as emitted. -/
def validatePublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.Prevalidated.validate)

/-- `vg_dsa_validate_private_key`, as emitted. -/
def validatePrivateKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.PrevalidatedSign.validate)

/-- `vg_dsa_verify_prevalidated`, as emitted. -/
def verifyPrevalidated : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Dsa.PPC64LE.Prevalidated.verify)

end VG.Impl.Dsa.PPC64LE.Fn
