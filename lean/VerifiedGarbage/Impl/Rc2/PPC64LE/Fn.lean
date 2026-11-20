module

public import VerifiedGarbage.Impl.Rc2.PPC64LE.Cbc
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Stream
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Rc2 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Rc2/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Rc2.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_rc2_cbc_init`, as emitted. -/
def cbcInit : Prog isa :=
  scrub 32 608 ⟨true, true, [.r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.init)

/-- `vg_rc2_cbc_encrypt_chained`, as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrub 0 544 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v4, .v5, .v6, .v7, .v8, .v9]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r7 64 Impl.Rc2.PPC64LE.Cbc.encrypt)

/-- `vg_rc2_cbc_decrypt_chained`, as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrub 0 544 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v4, .v5, .v6, .v7, .v8, .v9]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 544 .r7 64 Impl.Rc2.PPC64LE.Cbc.decrypt)

end VG.Impl.Rc2.PPC64LE.Fn
