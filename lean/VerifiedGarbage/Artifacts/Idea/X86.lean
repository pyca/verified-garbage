import VerifiedGarbage.Proof.Idea.X86.Verified

/-! # IDEA artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.Idea.X86

def artifacts : List Artifact := [
  { Spec.Idea.expandKeyApi with
    target := X86.target
    doc := Spec.Idea.expandKeyApi.doc
      (notes := ["Baseline IA-32: each 32-bit word of subkeys is a fixed bit permutation of the key's four words, assembled with rotations and masks, without branches."])
    code := Impl.Idea.X86.expandKey
    contract := Spec.Idea.expandKeyContract X86.abi
    stack := 0
    verified := Proof.Idea.X86.expandKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Idea.invertKeyApi with
    target := X86.target
    doc := Spec.Idea.invertKeyApi.doc
      (notes := ["Baseline IA-32: each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mul`, each reduced without branches."])
    code := Impl.StackScratch.X86.withStackScratch 32 2 Impl.Idea.X86.invertKey
    contract := Spec.Idea.invertKeyContract X86.abi 32
    stack := 32
    verified := Proof.Idea.X86.invertKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Idea.ecbApi with
    target := X86.target
    doc := Spec.Idea.ecbApi.doc
      (notes := ["Baseline IA-32, a block at a time in general-purpose registers, with the subkeys copied to a buffer on the stack (zeroed on return): each multiplication modulo 2^16 + 1 is a 32-bit `mul` of the residues and a reduction of the product less one, without branches."])
    code := Impl.StackScratch.X86.withStackScratchWiped 152 3 Proof.Idea.X86.wipedWords Impl.Idea.X86.ecb
    contract := Spec.Idea.ecbContract X86.abi 152
    stack := 152
    verified := Proof.Idea.X86.ecb_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Idea.X86
