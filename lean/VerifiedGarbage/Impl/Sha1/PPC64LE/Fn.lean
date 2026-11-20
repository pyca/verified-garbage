module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.Sha1.PPC64LE.Stream
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Sha1 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Sha1/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Sha1.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_sha1_update`, as emitted. -/
def update : Prog isa :=
  scrubAll 0 240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sha1.PPC64LE.Stream.update)

/-- `vg_sha1_finalize`, as emitted. -/
def finalize : Prog isa :=
  scrubAll 0 240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sha1.PPC64LE.Stream.finalize)

end VG.Impl.Sha1.PPC64LE.Fn
