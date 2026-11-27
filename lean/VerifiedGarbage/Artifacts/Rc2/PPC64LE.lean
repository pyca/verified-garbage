module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyVerified
import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Frame
import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Chained
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC2 on PPC64LE -/

namespace VG.Artifacts.Rc2.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Rc2.cbcInitApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.Fn.cbcInit
    verified := Proof.Rc2.PPC64LE.Scrub.cbcInit_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Rc2.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Rc2.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc2.PPC64LE
