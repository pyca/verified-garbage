module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.KeyInit
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# RsaKeyGen on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/RsaKeyGen/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_rsa_generate_init`, as emitted. -/
def keyInit : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.RsaKeyGen.PPC64LE.KeyInit.init)

end VG.Impl.RsaKeyGen.PPC64LE.Fn
