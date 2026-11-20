module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.Whole
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# Ed448 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Ed448/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Ed448.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_ed448_public_key`, as emitted. -/
def publicKey : Prog isa :=
  scrub 0 240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ed448.PPC64LE.Whole.publicKeyCode)

/-- `vg_ed448_sign_cached`, as emitted. -/
def signCached : Prog isa :=
  scrub 0 624 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ed448.PPC64LE.Whole.signCachedCode)

/-- `vg_ed448_verify`, as emitted. -/
def verify : Prog isa :=
  scrub 32 352 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ed448.PPC64LE.Whole.verifyCode)

end VG.Impl.Ed448.PPC64LE.Fn
