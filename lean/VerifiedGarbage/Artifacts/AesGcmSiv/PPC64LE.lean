module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Scrub
public import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-GCM-SIV (RFC 8452) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.PPC64LE

def artifacts : List Artifact := [
  Spec.GcmSiv.sealApi.artifact PPC64LE.target
    (Proof.AesGcmSiv.PPC64LE.Scrub.sealReg Proof.GcmSiv.Polyval.tagInput_eq_tagInputG),
  Spec.GcmSiv.openApi.artifact PPC64LE.target
    (Proof.AesGcmSiv.PPC64LE.Scrub.openReg Proof.GcmSiv.Polyval.tagInput_eq_tagInputG)]

end VG.Artifacts.AesGcmSiv.PPC64LE
