module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86_64

open VG.Proof.CmacTripleDes.X86_64

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 648 .rcx Impl.CmacTripleDes.Stream.X86_64.streamInit
    stack := 648
    verified := Proof.CmacTripleDes.Stream.X86_64.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 696 .r8 Impl.CmacTripleDes.Stream.X86_64.absorb
    stack := 696
    verified := Proof.CmacTripleDes.Stream.X86_64.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 648 .rcx Impl.CmacTripleDes.Stream.X86_64.finish
    stack := 648
    verified := Proof.CmacTripleDes.Stream.X86_64.finish_framed }]

end VG.Artifacts.CmacTripleDes.X86_64
