module

public import VerifiedGarbage.Impl.AesXts.PPC64LEUnit
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# AesXts on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/AesXts/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.AesXts.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_aes_xts_encrypt_unit`, as emitted. -/
def encryptUnit : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.AesXts.PPC64LEUnit.encrypt)

/-- `vg_aes_xts_decrypt_unit`, as emitted. -/
def decryptUnit : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.AesXts.PPC64LEUnit.decrypt)

end VG.Impl.AesXts.PPC64LE.Fn
