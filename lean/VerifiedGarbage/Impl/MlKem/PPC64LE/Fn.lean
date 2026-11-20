module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Codec
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Wipe
public import VerifiedGarbage.Impl.MlKem1024.PPC64LE.Poly
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# MlKem on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/MlKem/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.MlKem.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `Spec.MlKem.keyGenApi`'s function, as emitted. -/
def keyGen : Prog isa :=
  scrub 32 96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (Impl.MlKem.PPC64LE.Wipe.keyGen)

/-- `Spec.MlKem.encapsApi`'s function, as emitted. -/
def encaps : Prog isa :=
  scrub 32 96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (Impl.MlKem.PPC64LE.Wipe.encaps)

/-- `Spec.MlKem.encapsHApi`'s function, as emitted. -/
def encapsH : Prog isa :=
  scrub 32 96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (Impl.MlKem.PPC64LE.Wipe.encapsH)

/-- `Spec.MlKem.decapsApi`'s function, as emitted. -/
def decaps : Prog isa :=
  scrub 32 96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (Impl.MlKem.PPC64LE.Wipe.decaps)

/-- `Spec.MlKem.checkEkApi`'s function, as emitted. -/
def checkEk : Prog isa :=
  scrub 32 0 ⟨false, true, [.r4, .r5, .r6, .r7], false, []⟩
    (Impl.MlKem.PPC64LE.checkEk)

/-- `Spec.MlKem1024.checkEkApi`'s function, as emitted. -/
def checkEk1024 : Prog isa :=
  scrub 32 0 ⟨false, true, [.r4, .r5, .r6, .r7], false, []⟩
    (Impl.MlKem1024.PPC64LE.checkEk1024)

/-- `Spec.MlKem1024.keyGenApi`'s function, as emitted. -/
def keyGen1024 : Prog isa :=
  scrub 32 96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (Impl.MlKem.PPC64LE.Wipe.keyGen1024)

/-- `Spec.MlKem1024.encapsApi`'s function, as emitted. -/
def encaps1024 : Prog isa :=
  scrub 32 96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (Impl.MlKem.PPC64LE.Wipe.encaps1024)

/-- `Spec.MlKem1024.encapsHApi`'s function, as emitted. -/
def encapsH1024 : Prog isa :=
  scrub 32 96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (Impl.MlKem.PPC64LE.Wipe.encapsH1024)

/-- `Spec.MlKem1024.decapsApi`'s function, as emitted. -/
def decaps1024 : Prog isa :=
  scrub 32 96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (Impl.MlKem.PPC64LE.Wipe.decaps1024)

end VG.Impl.MlKem.PPC64LE.Fn
