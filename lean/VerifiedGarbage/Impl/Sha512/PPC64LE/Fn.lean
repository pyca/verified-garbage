module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Stream
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Sha512 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Sha512/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Sha512.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_sha512_update`, as emitted. -/
def update : Prog isa :=
  scrubAll 0 1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r7 Impl.Sha512.PPC64LE.Stream.update)

/-- `vg_sha512_finalize`, as emitted. -/
def finalize : Prog isa :=
  scrubAll 0 1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize)

/-- `vg_sha384_finalize`, as emitted. -/
def finalize384 : Prog isa :=
  scrubAll 0 1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize384)

/-- `vg_sha512_224_finalize`, as emitted. -/
def finalize512_224 : Prog isa :=
  scrubAll 0 1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_224)

/-- `vg_sha512_256_finalize`, as emitted. -/
def finalize512_256 : Prog isa :=
  scrubAll 0 1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_256)

end VG.Impl.Sha512.PPC64LE.Fn
