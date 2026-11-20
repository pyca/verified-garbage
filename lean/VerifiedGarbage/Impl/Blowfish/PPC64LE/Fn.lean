module

public import VerifiedGarbage.Impl.Blowfish.PPC64LE
public import VerifiedGarbage.Impl.Blowfish.PPC64LE.FbFinal
public import VerifiedGarbage.Impl.Blowfish.PPC64LE.Modes
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Blowfish on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Blowfish/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Blowfish.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_blowfish_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 64 .r6 4 Impl.Blowfish.PPC64LE.expandKey)

/-- `vg_blowfish_ecb_encrypt`, as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubAll 0 288 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.encrypt)

/-- `vg_blowfish_ecb_decrypt`, as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubAll 0 288 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.decrypt)

/-- `vg_blowfish_cbc_encrypt_chained`, as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cbcEncryptChained)

/-- `vg_blowfish_cbc_decrypt_chained`, as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cbcDecryptChained)

/-- `vg_blowfish_cfb64_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncrypt)

/-- `vg_blowfish_cfb64_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecrypt)

/-- `vg_blowfish_cfb64_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncryptFinal)

/-- `vg_blowfish_cfb64_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecryptFinal)

/-- `vg_blowfish_ofb`, as emitted. -/
def ofb : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.ofb)

/-- `vg_blowfish_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.ofbFinal)

end VG.Impl.Blowfish.PPC64LE.Fn
