module

public import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Fn
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.X86_64

open VG.Proof.CmacTripleDes.X86_64

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact X86_64.target { code := Impl.CmacTripleDes.X86_64.Fn.init, verified := Proof.CmacTripleDes.X86_64.Scrub.init_scrubbed, spSafe := Proof.CmacTripleDes.X86_64.Scrub.init_spSafe },
  Spec.Cmac.tdesAbsorbApi.artifact X86_64.target { code := Impl.CmacTripleDes.X86_64.Fn.absorb, verified := Proof.CmacTripleDes.X86_64.Scrub.absorb_scrubbed, spSafe := Proof.CmacTripleDes.X86_64.Scrub.absorb_spSafe },
  Spec.Cmac.tdesFinishApi.artifact X86_64.target { code := Impl.CmacTripleDes.X86_64.Fn.finish, verified := Proof.CmacTripleDes.X86_64.Scrub.finish_scrubbed, spSafe := Proof.CmacTripleDes.X86_64.Scrub.finish_spSafe }]

end VG.Artifacts.CmacTripleDes.X86_64
