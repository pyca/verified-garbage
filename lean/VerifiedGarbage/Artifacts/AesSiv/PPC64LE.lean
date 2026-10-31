module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-SIV (RFC 5297) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesSiv.PPC64LE

open VG.Proof.AesSiv.PPC64LE

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesSiv.PPC64LE.init
    stack := 2592
    verified := init_framed },
  Spec.Siv.encryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2608 .r10 Impl.AesSiv.PPC64LE.encrypt
    stack := 2608
    verified := encrypt_framed },
  Spec.Siv.decryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 2608 .r10 Impl.AesSiv.PPC64LE.decrypt
    stack := 2608
    verified := decrypt_framed }]

end VG.Artifacts.AesSiv.PPC64LE
