module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Seed.PPC64LE.FbFinal
public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Spec.Seed

/-!
# Seed on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Seed/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Seed.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_seed_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r5 130 Impl.Seed.PPC64LE.expandKey)

/-- `vg_seed_ecb_encrypt`, as emitted. -/
def ecbEncrypt : Prog isa :=
  scrub 0 1168 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .encrypt))

/-- `vg_seed_ecb_decrypt`, as emitted. -/
def ecbDecrypt : Prog isa :=
  scrub 0 1168 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .decrypt))

/-- `vg_seed_cbc_encrypt_chained`, as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cbcEncryptChained)

/-- `vg_seed_cbc_decrypt_chained`, as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1424 .r7 174 Impl.Seed.PPC64LE.cbcDecryptChained)

/-- `vg_seed_cfb128_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbEncrypt)

/-- `vg_seed_cfb128_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa :=
  scrub 0 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1424 .r7 174 Impl.Seed.PPC64LE.cfbDecrypt)

/-- `vg_seed_cfb128_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbEncryptFinal)

/-- `vg_seed_cfb128_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbDecryptFinal)

/-- `vg_seed_ofb`, as emitted. -/
def ofb : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofb)

/-- `vg_seed_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16]⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.ofbFinal)

end VG.Impl.Seed.PPC64LE.Fn
