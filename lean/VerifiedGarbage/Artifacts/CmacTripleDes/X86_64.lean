module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Fn
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86-64 -/

namespace VG.Artifacts.CmacTripleDes.X86_64

open VG.Proof.CmacTripleDes.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Cmac.tdesStreamInitApi.artifact X86_64.target { code := Impl.CmacTripleDes.X86_64.Fn.init, verified := Proof.CmacTripleDes.X86_64.Scrub.init_scrubbed, spSafe := Proof.CmacTripleDes.X86_64.Scrub.init_spSafe },
  Spec.Cmac.tdesAbsorbApi.artifact X86_64.target { code := Impl.CmacTripleDes.X86_64.Fn.absorb, verified := Proof.CmacTripleDes.X86_64.Scrub.absorb_scrubbed, spSafe := Proof.CmacTripleDes.X86_64.Scrub.absorb_spSafe },
  Spec.Cmac.tdesFinishApi.artifact X86_64.target { code := Impl.CmacTripleDes.X86_64.Fn.finish, verified := Proof.CmacTripleDes.X86_64.Scrub.finish_scrubbed, spSafe := Proof.CmacTripleDes.X86_64.Scrub.finish_spSafe }]

spec_apis artifacts

end VG.Artifacts.CmacTripleDes.X86_64
