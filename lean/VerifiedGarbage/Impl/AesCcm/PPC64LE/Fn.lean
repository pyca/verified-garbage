module

public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args

/-!
# AesCcm on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/AesCcm/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.AesCcm.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_aes_ccm_seal`, as emitted. -/
def «seal» : Prog isa :=
  scrubAll 0 576 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchArgs 576 2 Impl.AesCcm.PPC64LE.seal)

/-- `vg_aes_ccm_open`, as emitted. -/
def «open» : Prog isa :=
  scrubAll 32 576 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchArgs 576 2 Impl.AesCcm.PPC64LE.open)

end VG.Impl.AesCcm.PPC64LE.Fn
