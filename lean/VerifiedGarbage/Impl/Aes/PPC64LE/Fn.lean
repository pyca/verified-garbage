module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto
public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto.ExpandKey
public import VerifiedGarbage.Impl.AesCbc.PPC64LE.Wiped
public import VerifiedGarbage.Impl.AesCfb.PPC64LE
public import VerifiedGarbage.Impl.AesCfb.PPC64LE.Final
public import VerifiedGarbage.Impl.AesCfb8.PPC64LE
public import VerifiedGarbage.Impl.AesCtr.PPC64LE
public import VerifiedGarbage.Impl.AesCtr.PPC64LE.Final
public import VerifiedGarbage.Impl.AesOfb.PPC64LE
public import VerifiedGarbage.Impl.AesOfb.PPC64LE.Final
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Aes on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Aes/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_aes_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9]⟩
    (Impl.Aes.PPC64LE.Crypto.expandKey)

/-- `vg_aes_ecb_encrypt`, as emitted. -/
def ecbEncrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.Aes.PPC64LE.Crypto.encryptBlocks)

/-- `vg_aes_ecb_decrypt`, as emitted. -/
def ecbDecrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.Aes.PPC64LE.Crypto.decryptBlocks)

/-- `vg_aes_cbc_encrypt`, as emitted. -/
def cbcEncrypt : Prog isa :=
  scrub 0 48 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.AesCbc.PPC64LE.Wiped.encrypt)

/-- `vg_aes_cbc_decrypt`, as emitted. -/
def cbcDecrypt : Prog isa :=
  scrub 0 48 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v19]⟩
    (Impl.AesCbc.PPC64LE.Wiped.decrypt)

/-- `vg_aes_ctr`, as emitted. -/
def ctr : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (Impl.AesCtr.PPC64LE.crypt)

/-- `vg_aes_ctr_final`, as emitted. -/
def ctrFinal : Prog isa :=
  scrub 0 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 112 PPC64LE.Reg.r9 10 Impl.AesCtr.PPC64LE.cryptFinal)

/-- `vg_aes_cfb128_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.AesCfb.PPC64LE.encrypt)

/-- `vg_aes_cfb128_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.AesCfb.PPC64LE.decrypt)

/-- `vg_aes_cfb128_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 PPC64LE.Reg.r9 8 Impl.AesCfb.PPC64LE.encryptFinal)

/-- `vg_aes_cfb128_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 PPC64LE.Reg.r9 8 Impl.AesCfb.PPC64LE.decryptFinal)

/-- `vg_aes_cfb8_encrypt`, as emitted. -/
def cfb8Encrypt : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.AesCfb8.PPC64LE.encrypt)

/-- `vg_aes_cfb8_decrypt`, as emitted. -/
def cfb8Decrypt : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.AesCfb8.PPC64LE.decrypt)

/-- `vg_aes_ofb`, as emitted. -/
def ofb : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.AesOfb.PPC64LE.crypt)

/-- `vg_aes_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 PPC64LE.Reg.r9 8 Impl.AesOfb.PPC64LE.cryptFinal)

end VG.Impl.Aes.PPC64LE.Fn
