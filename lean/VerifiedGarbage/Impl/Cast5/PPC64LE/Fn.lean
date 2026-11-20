module

public import VerifiedGarbage.Impl.Cast5.PPC64LE
public import VerifiedGarbage.Impl.Cast5.PPC64LE.FbFinal
public import VerifiedGarbage.Impl.Cast5.PPC64LE.Modes
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Cast5 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Cast5/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Cast5.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_cast5_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r7, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.Cast5.PPC64LE.expandKey)

/-- `vg_cast5_ecb_encrypt`, as emitted. -/
def ecbEncrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r5, .r6, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.Cast5.PPC64LE.ecbEncrypt)

/-- `vg_cast5_ecb_decrypt`, as emitted. -/
def ecbDecrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r5, .r6, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.Cast5.PPC64LE.ecbDecrypt)

/-- `vg_cast5_cbc_encrypt_chained`, as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cbcEncryptChained)

/-- `vg_cast5_cbc_decrypt_chained`, as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cbcDecryptChained)

/-- `vg_cast5_cfb64_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncrypt)

/-- `vg_cast5_cfb64_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecrypt)

/-- `vg_cast5_cfb64_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncryptFinal)

/-- `vg_cast5_cfb64_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecryptFinal)

/-- `vg_cast5_ofb`, as emitted. -/
def ofb : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.ofb)

/-- `vg_cast5_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.ofbFinal)

end VG.Impl.Cast5.PPC64LE.Fn
