module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.X25519.PPC64LE.Base
public import VerifiedGarbage.Impl.X25519.PPC64LE.Fe51
public import VerifiedGarbage.Impl.Xdh.PPC64LE

/-!
# X25519 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/X25519/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.X25519.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_x25519_exchange`, as emitted. -/
def exchange : Prog isa :=
  scrubAll 32 48 ⟨true, true, [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Xdh.PPC64LE.exchange "vg_x25519" Impl.X25519.PPC64LE.Fe51.x25519 32)

/-- `vg_x25519_base`, as emitted. -/
def base : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.X25519.PPC64LE.Base.x25519Base)

end VG.Impl.X25519.PPC64LE.Fn
