module

public import VerifiedGarbage.Proof.Idea.X86_64.FbVerified

/-! # IDEA-CFB64 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.X86_64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `mul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic CFB of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  { Spec.Idea.cfbEncryptApi with
    target := X86_64.target
    doc := Spec.Idea.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbEncrypt
    contract := Spec.Idea.cfbEncryptContract X86_64.abi 184
    stack := 184
    verified := Proof.Idea.X86_64.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Idea.cfbDecryptApi with
    target := X86_64.target
    doc := Spec.Idea.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbDecrypt
    contract := Spec.Idea.cfbDecryptContract X86_64.abi 184
    stack := 184
    verified := Proof.Idea.X86_64.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.IdeaCfb.X86_64
