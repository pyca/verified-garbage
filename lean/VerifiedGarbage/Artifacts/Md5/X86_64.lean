module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Md5.X86_64.Shared

/-! # MD5 (RFC 1321) on x86-64 -/

@[expose] public section


namespace VG.Artifacts.Md5.X86_64

def artifacts : List Artifact := [
  { Spec.Md5.compressApi with
    target := X86_64.target
    doc := Spec.Md5.compressApi.doc
    code := Impl.Md5.X86_64.compress
    contract := Spec.Md5.compressContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.initApi with
    target := X86_64.target
    doc := Spec.Md5.initApi.doc
    code := Impl.Md5.X86_64.Stream.init
    contract := Spec.Md5.initContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.updateApi with
    target := X86_64.target
    doc := Spec.Md5.updateApi.doc
    code := Impl.StackScratch.X86_64.withStackScratch 120 .r8 Impl.Md5.X86_64.Stream.update
    contract := Spec.Md5.updateContract X86_64.abi (8 + 120)
    stack := 8 + 120
    verified := Proof.Md5.X86_64.Shared.update
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.finalizeApi with
    target := X86_64.target
    doc := Spec.Md5.finalizeApi.doc
    code := Impl.StackScratch.X86_64.withStackScratch 120 .rcx Impl.Md5.X86_64.Stream.finalize
    contract := Spec.Md5.finalizeContract X86_64.abi (8 + 120)
    stack := 8 + 120
    verified := Proof.Md5.X86_64.Shared.finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.updateScratchApi with
    target := X86_64.target
    doc := Spec.Md5.updateScratchApi.doc
    code := Impl.Md5.X86_64.Stream.update
    contract := Spec.Md5.updateScratchContract X86_64.abi 8
    stack := 8
    verified := Proof.Md5.X86_64.Shared.updateScratch
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.finalizeScratchApi with
    target := X86_64.target
    doc := Spec.Md5.finalizeScratchApi.doc
    code := Impl.Md5.X86_64.Stream.finalize
    contract := Spec.Md5.finalizeScratchContract X86_64.abi 8
    stack := 8
    verified := Proof.Md5.X86_64.Shared.finalizeScratch
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Md5.X86_64
