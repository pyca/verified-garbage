module

public import VerifiedGarbage.Proof.Sm3.X86.Shared
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm3.X86.Lit

/-! # SM3 (GB/T 32905-2016) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm3.X86

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact X86.target {
    code := Impl.Sm3.X86.Stream.init
    verified := Proof.Sm3.X86.Shared.init },
  Spec.Sm3.updateApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 188 5 Impl.Sm3.X86.Stream.update
    stack := 20 + 188
    verified := Proof.Sm3.X86.Shared.update },
  Spec.Sm3.finalizeApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 184 4 Impl.Sm3.X86.Stream.finalize
    stack := 20 + 184
    verified := Proof.Sm3.X86.Shared.finalize }]

end VG.Artifacts.Sm3.X86
