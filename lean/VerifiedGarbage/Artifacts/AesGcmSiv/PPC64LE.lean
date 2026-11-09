module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Law
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Verified
public import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # AES-GCM-SIV (RFC 8452) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.PPC64LE

open VG.Proof.AesGcmSiv.PPC64LE

def artifacts : List Artifact := [
  Spec.GcmSiv.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 Impl.AesGcmSiv.PPC64LE.«seal»
    stack := 3936
    verified := Proof.AesGcmSiv.seal_keyed (seal_framed Proof.GcmSiv.Polyval.tagInput_eq_tagInputG) },
  Spec.GcmSiv.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchArgs 3936 0 Impl.AesGcmSiv.PPC64LE.«open»
    stack := 3936
    verified := Proof.AesGcmSiv.open_keyed (open_framed Proof.GcmSiv.Polyval.tagInput_eq_tagInputG) }]

end VG.Artifacts.AesGcmSiv.PPC64LE
