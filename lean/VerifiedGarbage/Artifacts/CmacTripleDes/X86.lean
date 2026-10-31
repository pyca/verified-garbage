module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86.Update

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86

open VG.Proof.CmacTripleDes.X86

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 660 3 Impl.CmacTripleDes.Stream.X86.streamInit
    stack := 680
    verified := Proof.CmacTripleDes.Stream.X86.init_framed },
  Spec.Cmac.tdesAbsorbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 716 5 Impl.CmacTripleDes.Stream.X86.absorb
    stack := 740
    verified := Proof.CmacTripleDes.Stream.X86.absorb_framed },
  Spec.Cmac.tdesFinishApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 712 4 Impl.CmacTripleDes.Stream.X86.finish
    stack := 736
    verified := Proof.CmacTripleDes.Stream.X86.finish_framed }]

end VG.Artifacts.CmacTripleDes.X86
