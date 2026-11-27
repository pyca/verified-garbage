module

public import VerifiedGarbage.Impl.Argon2.PPC64LE.Derive
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# Argon2 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Argon2/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_argon2`, as emitted. -/
def derive : Prog isa :=
  scrubAll 0 384 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.Argon2.PPC64LE.Derive.derive)

end VG.Impl.Argon2.PPC64LE.Fn
