module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.FbFinal
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes

/-!
# TripleDes on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/TripleDes/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_triple_des_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.TripleDes.PPC64LE.Key.expandKey)

/-- `vg_triple_des_ecb_encrypt`, as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128 Impl.TripleDes.PPC64LE.Bitslice.encrypt)

/-- `vg_triple_des_ecb_decrypt`, as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128 Impl.TripleDes.PPC64LE.Bitslice.decrypt)

/-- `vg_triple_des_cbc_encrypt_chained`, as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cbcEncryptChained)

/-- `vg_triple_des_cbc_decrypt_chained`, as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1632 .r7 200 Impl.TripleDes.PPC64LE.cbcDecryptChained)

/-- `vg_triple_des_cfb64_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncrypt)

/-- `vg_triple_des_cfb64_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubAll 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1632 .r7 200 Impl.TripleDes.PPC64LE.cfbDecrypt)

/-- `vg_triple_des_cfb64_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncryptFinal)

/-- `vg_triple_des_cfb64_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbDecryptFinal)

/-- `vg_triple_des_cfb8_encrypt`, as emitted. -/
def cfb8Encrypt : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfb8Encrypt)

/-- `vg_triple_des_cfb8_decrypt`, as emitted. -/
def cfb8Decrypt : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfb8Decrypt)

/-- `vg_triple_des_ofb`, as emitted. -/
def ofb : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.ofb)

/-- `vg_triple_des_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrubAll 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.ofbFinal)

end VG.Impl.TripleDes.PPC64LE.Fn
