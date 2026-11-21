module

public import VerifiedGarbage.Impl.Ct.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# Ct on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Ct/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Ct.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_ct_eq`, as emitted. -/
def eq : Prog isa :=
  scrubAll 32 0 ⟨false, true, [.r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.Ct.PPC64LE.eq)

end VG.Impl.Ct.PPC64LE.Fn
