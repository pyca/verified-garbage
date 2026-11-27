module

public import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Md5 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Md5/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Md5.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_md5_update`, as emitted. -/
def update : Prog isa :=
  scrubAll 0 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 144 .r7 Impl.Md5.PPC64LE.Stream.update)

/-- `vg_md5_finalize`, as emitted. -/
def finalize : Prog isa :=
  scrubAll 0 192 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 144 .r6 Impl.Md5.PPC64LE.Stream.finalize)

end VG.Impl.Md5.PPC64LE.Fn
