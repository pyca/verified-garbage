module

public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact PPC64LE.target {
    code := Impl.AesOfb.PPC64LE.crypt
    verified := Proof.AesOfb.keyed Proof.AesOfb.PPC64LE.crypt_verified },
  Spec.Ofb.aesFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 Impl.AesOfb.PPC64LE.cryptFinal
    stack := 96
    verified := Proof.AesOfb.final_keyed Proof.AesOfb.PPC64LE.cryptFinal_framed }]

end VG.Artifacts.AesOfb.PPC64LE
