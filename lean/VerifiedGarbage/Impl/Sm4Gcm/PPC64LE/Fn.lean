module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args

/-!
# Sm4Gcm on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Sm4Gcm/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_sm4_gcm_init`, as emitted. -/
def init : Prog isa :=
  scrub 0 3616 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 320 .r5 (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r6 Impl.Sm4Gcm.PPC64LE.init))

/-- `vg_sm4_gcm_seal`, as emitted. -/
def «seal» : Prog isa :=
  scrub 0 3776 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchArgs 400 0 (Impl.StackScratch.PPC64LE.withStackScratchArgs 3376 1 Impl.Sm4Gcm.PPC64LE.seal))

/-- `vg_sm4_gcm_open`, as emitted. -/
def «open» : Prog isa :=
  scrub 32 3792 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchArgs 400 1 (Impl.StackScratch.PPC64LE.withStackScratchArgs 3392 2 Impl.Sm4Gcm.PPC64LE.open))

/-- `vg_sm4_gcm_stream_init`, as emitted. -/
def streamInit : Prog isa :=
  scrub 0 320 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 320 .r7 Impl.AesGcm.PPC64LE.streamInit)

/-- `vg_sm4_gcm_stream_aad`, as emitted. -/
def streamAad : Prog isa :=
  scrub 0 320 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 320 .r8 Impl.AesGcm.PPC64LE.streamAad)

/-- `vg_sm4_gcm_stream_encrypt`, as emitted. -/
def streamEncrypt : Prog isa :=
  scrub 0 3616 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 320 .r9 (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamEncrypt))

/-- `vg_sm4_gcm_stream_decrypt`, as emitted. -/
def streamDecrypt : Prog isa :=
  scrub 0 3616 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 320 .r9 (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamDecrypt))

/-- `vg_sm4_gcm_stream_finish`, as emitted. -/
def streamFinish : Prog isa :=
  scrub 0 3616 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 320 .r8 (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r9 Impl.Sm4Gcm.PPC64LE.streamFinish))

/-- `vg_sm4_gcm_stream_verify`, as emitted. -/
def streamVerify : Prog isa :=
  scrub 32 3616 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 320 .r9 (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 Impl.Sm4Gcm.PPC64LE.streamVerify))

end VG.Impl.Sm4Gcm.PPC64LE.Fn
