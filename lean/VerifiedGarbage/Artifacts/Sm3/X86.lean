import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sm3.X86.Shared

/-! # SM3 (GB/T 32905-2016) on x86 -/

namespace VG.Artifacts.Sm3.X86

def artifacts : List Artifact := [
  { Spec.Sm3.compressApi with
    target := X86.target
    doc := Spec.Sm3.compressApi.doc
    code := Impl.Sm3.X86.compress
    contract := Spec.Sm3.compressContract X86.abi
    verified := Proof.Sm3.X86.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm3.initApi with
    target := X86.target
    doc := Spec.Sm3.initApi.doc
    code := Impl.Sm3.X86.Stream.init
    contract := Spec.Sm3.initContract X86.abi
    verified := Proof.Sm3.X86.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm3.updateApi with
    target := X86.target
    doc := Spec.Sm3.updateApi.doc
    code := Impl.StackScratch.X86.withStackScratch 188 5 Impl.Sm3.X86.Stream.update
    contract := Spec.Sm3.updateContract X86.abi (20 + 188)
    stack := 20 + 188
    verified := Proof.Sm3.X86.Shared.update
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm3.finalizeApi with
    target := X86.target
    doc := Spec.Sm3.finalizeApi.doc
    code := Impl.StackScratch.X86.withStackScratch 184 4 Impl.Sm3.X86.Stream.finalize
    contract := Spec.Sm3.finalizeContract X86.abi (20 + 184)
    stack := 20 + 184
    verified := Proof.Sm3.X86.Shared.finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sm3.X86
