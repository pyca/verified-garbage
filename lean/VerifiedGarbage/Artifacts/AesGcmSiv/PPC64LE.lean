module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Scrub
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-GCM-SIV (RFC 8452) on PPC64LE -/

namespace VG.Artifacts.AesGcmSiv.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.GcmSiv.sealApi.artifact PPC64LE.target {
    code := Impl.AesGcmSiv.PPC64LE.Fn.seal
    verified := Proof.AesGcmSiv.PPC64LE.Scrub.seal_scrubbed Proof.GcmSiv.Polyval.tagInput_eq_tagInputG },
  Spec.GcmSiv.openApi.artifact PPC64LE.target {
    code := Impl.AesGcmSiv.PPC64LE.Fn.open
    verified := Proof.AesGcmSiv.PPC64LE.Scrub.open_scrubbed Proof.GcmSiv.Polyval.tagInput_eq_tagInputG }]

spec_apis artifacts

end VG.Artifacts.AesGcmSiv.PPC64LE
