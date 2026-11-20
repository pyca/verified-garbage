module

public import VerifiedGarbage.Impl.CmacAes.Stream.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# CmacAes Stream on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/CmacAes/Stream/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.CmacAes.Stream.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_cmac_aes_init`, as emitted. -/
def init : Prog isa :=
  scrub 0 160 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 160 .r6 Impl.CmacAes.Stream.PPC64LE.init)

/-- `vg_cmac_aes_absorb`, as emitted. -/
def absorb : Prog isa :=
  scrub 0 160 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 160 .r8 Impl.CmacAes.Stream.PPC64LE.absorb)

/-- `vg_cmac_aes_finish`, as emitted. -/
def finish : Prog isa :=
  scrub 0 160 ⟨true, false, [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 160 .r7 Impl.CmacAes.Stream.PPC64LE.finish)

end VG.Impl.CmacAes.Stream.PPC64LE.Fn
