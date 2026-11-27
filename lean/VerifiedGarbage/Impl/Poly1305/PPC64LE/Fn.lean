module

public import VerifiedGarbage.Impl.Poly1305.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Poly1305 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Poly1305/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Poly1305.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_poly1305_init`, as emitted. -/
def init : Prog isa :=
  scrubAll 0 0 ⟨false, false, [.r5, .r6, .r7, .r8], false, []⟩
    (Impl.Poly1305.PPC64LE.init)

/-- `vg_poly1305_update`, as emitted. -/
def update : Prog isa :=
  scrubAll 0 160 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 160 .r7 Impl.Poly1305.PPC64LE.update)

/-- `vg_poly1305_finalize`, as emitted. -/
def finalize : Prog isa :=
  scrubAll 0 160 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 160 .r6 Impl.Poly1305.PPC64LE.finalize)

end VG.Impl.Poly1305.PPC64LE.Fn
