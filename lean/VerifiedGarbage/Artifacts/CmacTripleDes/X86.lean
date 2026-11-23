module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Scrub
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact X86.target {
    code := Impl.CmacTripleDes.Stream.X86.Fn.init
    verified := Proof.CmacTripleDes.Stream.X86.Scrub.init_scrubbed },
  Spec.Cmac.tdesAbsorbApi.artifact X86.target {
    code := Impl.CmacTripleDes.Stream.X86.Fn.absorb
    verified := Proof.CmacTripleDes.Stream.X86.Scrub.absorb_scrubbed },
  Spec.Cmac.tdesFinishApi.artifact X86.target {
    code := Impl.CmacTripleDes.Stream.X86.Fn.finish
    verified := Proof.CmacTripleDes.Stream.X86.Scrub.finish_scrubbed }]

end VG.Artifacts.CmacTripleDes.X86
