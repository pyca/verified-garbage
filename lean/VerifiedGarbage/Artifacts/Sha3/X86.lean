import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha3.X86.Shared
import VerifiedGarbage.Proof.Sha3.X86.Frame

/-! # SHA-3 and SHAKE (FIPS 202) on x86 -/

namespace VG.Artifacts.Sha3.X86

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := X86.target
    doc := Spec.Sha3.permuteApi.doc
    code := Impl.Sha3.X86.permute
    contract := Spec.Sha3.permuteContract X86.abi
    verified := Proof.Sha3.X86.Shared.permute
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.absorbApi with
    target := X86.target
    doc := Spec.Sha3.absorbApi.doc
    code := Impl.StackScratch.X86.withStackScratch 668 5 Impl.Sha3.X86.Stream.absorb
    contract := Spec.Sha3.absorbContract X86.abi 680
    stack := 680
    verified := Proof.Sha3.X86.Frame.absorb_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.absorbScratchApi with
    target := X86.target
    doc := Spec.Sha3.absorbScratchApi.doc
    code := Impl.Sha3.X86.Stream.absorb
    contract := Spec.Sha3.absorbScratchContract X86.abi 12
    stack := 12
    verified := Proof.Sha3.X86.Shared.absorb
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.padApi with
    target := X86.target
    doc := Spec.Sha3.padApi.doc
    code := Impl.StackScratch.X86.withStackScratch 664 4 Impl.Sha3.X86.Stream.pad
    contract := Spec.Sha3.padContract X86.abi 676
    stack := 676
    verified := Proof.Sha3.X86.Frame.pad_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.padScratchApi with
    target := X86.target
    doc := Spec.Sha3.padScratchApi.doc
    code := Impl.Sha3.X86.Stream.pad
    contract := Spec.Sha3.padScratchContract X86.abi 12
    stack := 12
    verified := Proof.Sha3.X86.Shared.pad
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.squeezeApi with
    target := X86.target
    doc := Spec.Sha3.squeezeApi.doc
    code := Impl.StackScratch.X86.withStackScratch 668 5 Impl.Sha3.X86.Stream.squeeze
    contract := Spec.Sha3.squeezeContract X86.abi 680
    stack := 680
    verified := Proof.Sha3.X86.Frame.squeeze_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha3.squeezeScratchApi with
    target := X86.target
    doc := Spec.Sha3.squeezeScratchApi.doc
    code := Impl.Sha3.X86.Stream.squeeze
    contract := Spec.Sha3.squeezeScratchContract X86.abi 12
    stack := 12
    verified := Proof.Sha3.X86.Shared.squeeze
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha3.X86
