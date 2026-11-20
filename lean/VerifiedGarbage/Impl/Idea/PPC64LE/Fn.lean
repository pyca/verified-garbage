module

public import VerifiedGarbage.Impl.Idea.PPC64LE
public import VerifiedGarbage.Impl.Idea.PPC64LE.FbFinal
public import VerifiedGarbage.Impl.Idea.PPC64LE.Modes
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# Idea on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Idea/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Idea.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_idea_expand_key`, as emitted. -/
def expandKey : Prog isa :=
  scrub 0 0 ⟨false, false, [.r10, .r11, .r12], false, []⟩
    (Impl.Idea.PPC64LE.expandKey)

/-- `vg_idea_invert_key`, as emitted. -/
def invertKey : Prog isa :=
  scrub 0 0 ⟨true, false, [.r5, .r6, .r7, .r8, .r9, .r11, .r12], false, []⟩
    (Impl.Idea.PPC64LE.invertKey)

/-- `vg_idea_ecb`, as emitted. -/
def ecb : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.Idea.PPC64LE.ecb)

/-- `vg_idea_cbc_encrypt_chained`, as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cbcEncryptChained)

/-- `vg_idea_cbc_decrypt_chained`, as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cbcDecryptChained)

/-- `vg_idea_cfb64_encrypt`, as emitted. -/
def cfbEncrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbEncrypt)

/-- `vg_idea_cfb64_decrypt`, as emitted. -/
def cfbDecrypt : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbDecrypt)

/-- `vg_idea_cfb64_encrypt_final`, as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbEncryptFinal)

/-- `vg_idea_cfb64_decrypt_final`, as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbDecryptFinal)

/-- `vg_idea_ofb`, as emitted. -/
def ofb : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.ofb)

/-- `vg_idea_ofb_final`, as emitted. -/
def ofbFinal : Prog isa :=
  scrub 0 0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.ofbFinal)

end VG.Impl.Idea.PPC64LE.Fn
