module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.CtrFinal
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Ecb
public import VerifiedGarbage.Impl.Camellia.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Camellia.PPC64LE.FbFinal
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Modes
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Camellia on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Camellia/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Camellia.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_camellia_cbc_encrypt_chained`, as emitted. -/
def cbcEnc : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cbcEncryptChained)

/-- `vg_camellia_cbc_decrypt_chained`, as emitted. -/
def cbcDec : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cbcDecryptChained)

/-- `vg_camellia_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r6, .r7, .r8, .r9, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r6 414 Impl.Camellia.PPC64LE.expandKey)

/-- `vg_camellia_ecb_encrypt`, as emitted. -/
def ecbEnc : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414 (Impl.Camellia.PPC64LE.ecb .encrypt))

/-- `vg_camellia_ecb_decrypt`, as emitted. -/
def ecbDec : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414 (Impl.Camellia.PPC64LE.ecb .decrypt))

/-- `vg_camellia_cfb128_encrypt`, as emitted. -/
def cfbEnc : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbEncrypt)

/-- `vg_camellia_cfb128_decrypt`, as emitted. -/
def cfbDec : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbDecrypt)

/-- `vg_camellia_cfb128_encrypt_final`, as emitted. -/
def cfbEncFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbEncryptFinal)

/-- `vg_camellia_cfb128_decrypt_final`, as emitted. -/
def cfbDecFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbDecryptFinal)

/-- `vg_camellia_ofb`, as emitted. -/
def ofb : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ofb)

/-- `vg_camellia_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ofbFinal)

/-- `vg_camellia_ctr`, as emitted. -/
def ctr : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ctr)

/-- `vg_camellia_ctr_final`, as emitted. -/
def ctrFinal : Prog isa :=
  scrubAll 0 3520 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r8 10 Impl.Camellia.PPC64LE.ctrFinal)

end VG.Impl.Camellia.PPC64LE.Fn
