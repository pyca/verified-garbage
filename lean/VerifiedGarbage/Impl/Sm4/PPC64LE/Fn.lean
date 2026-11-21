module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ctr
public import VerifiedGarbage.Impl.Sm4.PPC64LE.CtrFinal
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ecb
public import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Sm4.PPC64LE.FbFinal
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Modes
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Sm4 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Sm4/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_sm4_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r5 402 Impl.Sm4.PPC64LE.expandKey)

/-- `vg_sm4_ecb_encrypt`, as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .encrypt))

/-- `vg_sm4_ecb_decrypt`, as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r6 402 (Impl.Sm4.PPC64LE.ecb .decrypt))

/-- `vg_sm4_cbc_encrypt_chained`, as emitted. -/
def cbcEncrypt : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cbcEncryptChained)

/-- `vg_sm4_cbc_decrypt_chained`, as emitted. -/
def cbcDecrypt : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cbcDecryptChained)

/-- `vg_sm4_cfb128_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncrypt)

/-- `vg_sm4_cfb128_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecrypt)

/-- `vg_sm4_cfb128_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbEncryptFinal)

/-- `vg_sm4_cfb128_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cfbDecryptFinal)

/-- `vg_sm4_ofb`, as emitted. -/
def ofb : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofb)

/-- `vg_sm4_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofbFinal)

/-- `vg_sm4_ctr`, as emitted. -/
def ctr : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ctr)

/-- `vg_sm4_ctr_final`, as emitted. -/
def ctrFinal : Prog isa :=
  scrubAll 0 3408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v12, .v13, .v14, .v15]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r7 10 Impl.Sm4.PPC64LE.ctrFinal)

end VG.Impl.Sm4.PPC64LE.Fn
