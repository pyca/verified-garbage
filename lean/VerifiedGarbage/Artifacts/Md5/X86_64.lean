module

public import VerifiedGarbage.Proof.Md5.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Residue
import VerifiedGarbage.Proof.Md5.X86_64.Lit

/-! # MD5 (RFC 1321) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Md5.X86_64

def artifacts : List Artifact := [
  Spec.Md5.compressApi.artifact X86_64.target {
    code := Impl.Md5.X86_64.compress
    verified := Proof.Md5.X86_64.Shared.compress
    noResidue := true },
  Spec.Md5.initApi.artifact X86_64.target {
    code := Impl.Md5.X86_64.Stream.init
    verified := Proof.Md5.X86_64.Shared.init },
  Spec.Md5.updateApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 120 .r8 Impl.Md5.X86_64.Stream.update
    stack := 8 + 120
    verified := Proof.Md5.X86_64.Shared.update },
  Spec.Md5.finalizeApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 120 .rcx Impl.Md5.X86_64.Stream.finalize
    stack := 8 + 120
    verified := Proof.Md5.X86_64.Shared.finalize },
  Spec.Md5.updateScratchApi.artifact X86_64.target {
    code := Impl.Md5.X86_64.Stream.update
    stack := 8
    verified := Proof.Md5.X86_64.Shared.updateScratch },
  Spec.Md5.finalizeScratchApi.artifact X86_64.target {
    code := Impl.Md5.X86_64.Stream.finalize
    stack := 8
    verified := Proof.Md5.X86_64.Shared.finalizeScratch }]

end VG.Artifacts.Md5.X86_64
