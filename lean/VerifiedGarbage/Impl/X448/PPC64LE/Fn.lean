module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.X448.PPC64LE
public import VerifiedGarbage.Impl.Xdh.PPC64LE

/-!
# X448 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/X448/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.X448.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_x448_exchange`, as emitted. -/
def exchange : Prog isa :=
  scrub 32 48 ⟨true, true, [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Xdh.PPC64LE.exchange "vg_x448" Impl.X448.PPC64LE.x448 56)

/-- `vg_x448_base`, as emitted. -/
def base : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.X448.PPC64LE.x448Base)

end VG.Impl.X448.PPC64LE.Fn
