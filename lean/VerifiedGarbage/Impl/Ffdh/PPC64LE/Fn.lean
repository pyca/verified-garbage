module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.CheckPrivate
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Derive
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Domain
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# Ffdh on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Ffdh/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_ffdh_check_public`, as emitted. -/
def checkPublic : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Ffdh.PPC64LE.Domain.checkPublic)

/-- `vg_ffdh_exchange`, as emitted. -/
def exchange : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Ffdh.PPC64LE.Domain.exchange)

/-- `vg_ffdh_derive_public`, as emitted. -/
def derivePublic : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Ffdh.PPC64LE.Derive.derivePublic)

/-- `vg_ffdh_check_private`, as emitted. -/
def checkPrivate : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Ffdh.PPC64LE.CheckPrivate.checkPrivate)

/-- `vg_ffdh_generate_key_precompute`, as emitted. -/
def precompute : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Ffdh.PPC64LE.Cached.Precompute.code)

end VG.Impl.Ffdh.PPC64LE.Fn
