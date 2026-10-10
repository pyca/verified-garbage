import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sm3.X86_64.Shared

/-! # SM3 (GB/T 32905-2016) on x86-64 -/

namespace VG.Artifacts.Sm3.X86_64

def artifacts : List Artifact := [
  { Spec.Sm3.compressApi with
    target := X86_64.target
    doc := Spec.Sm3.compressApi.doc
    code := Impl.Sm3.X86_64.compress
    contract := Spec.Sm3.compressContract X86_64.abi
    verified := Proof.Sm3.X86_64.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm3.initApi with
    target := X86_64.target
    doc := Spec.Sm3.initApi.doc
    code := Impl.Sm3.X86_64.Stream.init
    contract := Spec.Sm3.initContract X86_64.abi
    verified := Proof.Sm3.X86_64.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm3.updateApi with
    target := X86_64.target
    doc := Spec.Sm3.updateApi.doc
    code := Impl.StackScratch.X86_64.withStackScratch 168 .r8 Impl.Sm3.X86_64.Stream.update
    contract := Spec.Sm3.updateContract X86_64.abi (8 + 168)
    stack := 8 + 168
    verified := Proof.Sm3.X86_64.Shared.update
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm3.finalizeApi with
    target := X86_64.target
    doc := Spec.Sm3.finalizeApi.doc
    code := Impl.StackScratch.X86_64.withStackScratch 168 .rcx Impl.Sm3.X86_64.Stream.finalize
    contract := Spec.Sm3.finalizeContract X86_64.abi (8 + 168)
    stack := 8 + 168
    verified := Proof.Sm3.X86_64.Shared.finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sm3.X86_64
