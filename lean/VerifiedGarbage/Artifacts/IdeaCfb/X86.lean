import VerifiedGarbage.Proof.Idea.X86.FbVerified

/-! # IDEA-CFB artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.IdeaCfb.X86

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, with branch-free ⊙ (`mul`, whose timing does not depend on its \
  operands), the subkeys copied to the stack once per call. The mode is the generic CFB of `Impl/Modes/X86/`, \
  over IDEA's ECB block."

def artifacts : List Artifact := [
  { Spec.Idea.cfbEncryptApi with
    target := X86.target
    doc := Spec.Idea.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbEncrypt
    contract := Spec.Idea.cfbEncryptContract X86.abi 208
    stack := 208
    verified := Proof.Idea.X86.Fb.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Idea.cfbDecryptApi with
    target := X86.target
    doc := Spec.Idea.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbDecrypt
    contract := Spec.Idea.cfbDecryptContract X86.abi 208
    stack := 208
    verified := Proof.Idea.X86.Fb.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.IdeaCfb.X86
