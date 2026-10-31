module

public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Verified
public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CMAC (NIST SP 800-38B) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CmacAes.PPC64LE

open VG.Proof.CmacAes.PPC64LE

def artifacts : List Artifact := [
  Spec.Cmac.aesSubkeysApi.artifact PPC64LE.target {
    code := Impl.CmacAes.PPC64LE.subkeys
    verified := subkeys_verified },
  Spec.Cmac.aesUpdateApi.artifact PPC64LE.target {
    code := Impl.CmacAes.PPC64LE.update
    verified := update_verified },
  Spec.Cmac.aesFinalizeApi.artifact PPC64LE.target {
    code := Impl.CmacAes.PPC64LE.finalize
    verified := finalize_verified },
  Spec.Cmac.aesInitApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r6 Impl.CmacAes.Stream.PPC64LE.init
    stack := 2336
    verified := Proof.CmacAes.Stream.PPC64LE.init_framed },
  Spec.Cmac.aesAbsorbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r8 Impl.CmacAes.Stream.PPC64LE.absorb
    stack := 2336
    verified := Proof.CmacAes.Stream.PPC64LE.absorb_framed },
  Spec.Cmac.aesFinishApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2336 .r7 Impl.CmacAes.Stream.PPC64LE.finish
    stack := 2336
    verified := Proof.CmacAes.Stream.PPC64LE.finish_framed }]

end VG.Artifacts.CmacAes.PPC64LE
