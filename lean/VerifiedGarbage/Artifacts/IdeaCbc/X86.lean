module

public import VerifiedGarbage.Proof.Idea.X86.CbcVerified

/-! # IDEA-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.X86

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, with branch-free ⊙ (`mul`, whose timing does not depend on its \
  operands), the subkeys copied to the stack once per call. The mode is the generic CBC of `Impl/Modes/X86/`, \
  over IDEA's ECB block."

def artifacts : List Artifact := [
  { Spec.Idea.cbcEncryptApi with
    target := X86.target
    doc := Spec.Idea.cbcEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cbcEncrypt
    contract := Spec.Idea.cbcEncryptContract X86.abi 208
    stack := 208
    verified := Proof.Idea.X86.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Idea.cbcDecryptApi with
    target := X86.target
    doc := Spec.Idea.cbcDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cbcDecrypt
    contract := Spec.Idea.cbcDecryptContract X86.abi 208
    stack := 208
    verified := Proof.Idea.X86.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.IdeaCbc.X86
