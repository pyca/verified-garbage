module

public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CTR (NIST SP 800-38A §6.5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCtr.PPC64LE

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact PPC64LE.target {
    code := Impl.AesCtr.PPC64LE.crypt
    verified := Proof.AesCtr.keyed Proof.AesCtr.PPC64LE.crypt_verified },
  Spec.Ctr.aesFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r9 10 Impl.AesCtr.PPC64LE.cryptFinal
    stack := 112
    verified := Proof.AesCtr.final_keyed Proof.AesCtr.PPC64LE.Final.cryptFinal_framed }]

end VG.Artifacts.AesCtr.PPC64LE
