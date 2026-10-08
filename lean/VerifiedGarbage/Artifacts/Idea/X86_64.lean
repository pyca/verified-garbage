import VerifiedGarbage.Proof.Idea.X86_64.Invert

/-! # IDEA artifacts on baseline x86-64 -/

namespace VG.Artifacts.Idea.X86_64

def artifacts : List Artifact := [
  { Spec.Idea.expandKeyApi with
    target := X86_64.target
    doc := Spec.Idea.expandKeyApi.doc
      (notes := ["Baseline x86-64: each quadword of subkeys is a fixed bit permutation of the key's two quadwords, assembled with rotations and masks, without branches."])
    code := Impl.Idea.X86_64.expandKey
    contract := Spec.Idea.expandKeyContract X86_64.abi
    stack := 0
    verified := Proof.Idea.X86_64.expandKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Idea.invertKeyApi with
    target := X86_64.target
    doc := Spec.Idea.invertKeyApi.doc
      (notes := ["Baseline x86-64: each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mul`, each reduced without branches."])
    code := Impl.Idea.X86_64.invertKey
    contract := Spec.Idea.invertKeyContract X86_64.abi
    stack := 0
    verified := Proof.Idea.X86_64.invertKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Idea.ecbApi with
    target := X86_64.target
    doc := Spec.Idea.ecbApi.doc
      (notes := ["Baseline x86-64, a block at a time in general-purpose registers: each multiplication modulo 2^16 + 1 is a `mul` and a reduction without branches."])
    code := Impl.StackScratch.X86_64.withStackScratch 24 .rcx Impl.Idea.X86_64.ecb
    contract := Spec.Idea.ecbContract X86_64.abi 24
    stack := 24
    verified := Proof.Idea.X86_64.ecb_framed
    spSafe := X86_64.withStackScratch_spSafe (by decide) (Code.all_of_allInstrs (by lit_decide)) }]

end VG.Artifacts.Idea.X86_64
