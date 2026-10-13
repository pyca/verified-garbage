module

public import VerifiedGarbage.Proof.Idea.AArch64.FbVerified

/-! # IDEA-CFB64 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.AArch64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `mul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic CFB of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.Idea.cfbEncryptApi with
    target := AArch64.target
    doc := Spec.Idea.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbEncrypt
    contract := Spec.Idea.cfbEncryptContract AArch64.abi 208
    stack := 208
    verified := Proof.Idea.AArch64.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Idea.cfbDecryptApi with
    target := AArch64.target
    doc := Spec.Idea.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cfbDecrypt
    contract := Spec.Idea.cfbDecryptContract AArch64.abi 208
    stack := 208
    verified := Proof.Idea.AArch64.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.IdeaCfb.AArch64
