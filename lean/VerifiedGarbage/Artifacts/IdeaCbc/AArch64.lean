import VerifiedGarbage.Proof.Idea.AArch64.CbcVerified

/-! # IDEA-CBC artifacts on baseline AArch64 -/

namespace VG.Artifacts.IdeaCbc.AArch64

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through `vg_idea_ecb`'s block code (inlined): ⊙ by `mul` and a \
  branchless reduction, no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic CBC of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.Idea.cbcEncryptApi with
    target := AArch64.target
    doc := Spec.Idea.cbcEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcEncrypt
    contract := Spec.Idea.cbcEncryptContract AArch64.abi 208
    stack := 208
    verified := Proof.Idea.AArch64.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Idea.cbcDecryptApi with
    target := AArch64.target
    doc := Spec.Idea.cbcDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 Impl.Idea.AArch64.cbcDecrypt
    contract := Spec.Idea.cbcDecryptContract AArch64.abi 208
    stack := 208
    verified := Proof.Idea.AArch64.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.IdeaCbc.AArch64
