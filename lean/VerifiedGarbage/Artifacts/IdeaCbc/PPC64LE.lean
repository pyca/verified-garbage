module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit

/-! # IDEA-CBC artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.PPC64LE

/-- How the functions compute IDEA, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, with ECB's verified block code inlined (each multiplication modulo 2^16 + 1 a `mulld` of the residues and a reduction of the product from its halves, without branches), reading the subkeys in place. The mode is the generic one of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31`, with its working space on the stack, zeroed before returning."

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact PPC64LE.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cbcEncryptChained
    stack := 96
    verified := Proof.Idea.PPC64LE.cbcEnc_framed Proof.Idea.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.Idea.cbcDecryptChainedApi.artifact PPC64LE.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cbcDecryptChained
    stack := 96
    verified := Proof.Idea.PPC64LE.cbcDec_framed Proof.Idea.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.IdeaCbc.PPC64LE
