module

public import VerifiedGarbage.Impl.AesSiv.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# AesSiv on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/AesSiv/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.AesSiv.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_aes_siv_init`, as emitted. -/
def init : Prog isa :=
  scrub 0 144 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 144 .r6 Impl.AesSiv.PPC64LE.init)

/-- `vg_aes_siv_encrypt`, as emitted. -/
def encrypt : Prog isa :=
  scrub 0 480 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 480 .r10 Impl.AesSiv.PPC64LE.encrypt)

/-- `vg_aes_siv_decrypt`, as emitted. -/
def decrypt : Prog isa :=
  scrub 32 480 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 480 .r10 Impl.AesSiv.PPC64LE.decrypt)

end VG.Impl.AesSiv.PPC64LE.Fn
