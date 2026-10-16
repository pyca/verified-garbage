module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Sm3.X86_64.Shared
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM3 (GB/T 32905-2016) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm3.X86_64

def artifacts : List Artifact := [
  Spec.Sm3.compressApi.artifact X86_64.target {
    code := Impl.Sm3.X86_64.compress
    verified := Proof.Sm3.X86_64.Shared.compress },
  Spec.Sm3.initApi.artifact X86_64.target {
    code := Impl.Sm3.X86_64.Stream.init
    verified := Proof.Sm3.X86_64.Shared.init },
  Spec.Sm3.updateApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 168 .r8 Impl.Sm3.X86_64.Stream.update
    stack := 8 + 168
    verified := Proof.Sm3.X86_64.Shared.update },
  Spec.Sm3.finalizeApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 168 .rcx Impl.Sm3.X86_64.Stream.finalize
    stack := 8 + 168
    verified := Proof.Sm3.X86_64.Shared.finalize }]

end VG.Artifacts.Sm3.X86_64
