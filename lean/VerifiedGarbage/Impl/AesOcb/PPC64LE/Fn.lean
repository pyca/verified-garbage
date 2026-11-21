module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args

/-!
# AesOcb on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/AesOcb/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.AesOcb.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_aes_ocb_init`, as emitted. -/
def init : Prog isa :=
  scrubAll 0 320 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 320 .r6 Impl.AesGcm.PPC64LE.init)

/-- `vg_aes_ocb_seal`, as emitted. -/
def «seal» : Prog isa :=
  scrubAll 0 640 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchArgs 640 2 Impl.AesOcb.PPC64LE.seal)

/-- `vg_aes_ocb_open`, as emitted. -/
def «open» : Prog isa :=
  scrubAll 32 640 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchArgs 640 2 Impl.AesOcb.PPC64LE.open)

end VG.Impl.AesOcb.PPC64LE.Fn
