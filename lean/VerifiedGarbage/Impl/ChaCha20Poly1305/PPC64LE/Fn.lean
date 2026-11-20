module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE
public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE.SealGather
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args

/-!
# ChaCha20Poly1305 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/ChaCha20Poly1305/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_chacha20_poly1305_seal`, as emitted. -/
def «seal» : Prog isa :=
  scrub 0 848 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 688 PPC64LE.Reg.r10 82 (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.seal))

/-- `vg_chacha20_poly1305_open`, as emitted. -/
def «open» : Prog isa :=
  scrub 32 848 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 688 PPC64LE.Reg.r10 82 (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.open))

/-- `vg_chacha20_poly1305_open_to`, as emitted. -/
def openTo : Prog isa :=
  scrub 32 928 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchArgsWiped 768 1 82 Impl.ChaCha20Poly1305.PPC64LE.openTo)

/-- `vg_chacha20_poly1305_seal_gather`, as emitted. -/
def sealGather : Prog isa :=
  scrub 0 928 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.ChaCha20Poly1305.PPC64LE.SealGather.sealGather)

end VG.Impl.ChaCha20Poly1305.PPC64LE.Fn
