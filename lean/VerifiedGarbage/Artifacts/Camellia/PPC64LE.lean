module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Verified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Camellia on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Camellia.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r6 414 Impl.Camellia.PPC64LE.expandKey
    verified := Proof.Camellia.PPC64LE.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414
      (Impl.Camellia.PPC64LE.ecb .encrypt)
    verified := Proof.Camellia.PPC64LE.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414
      (Impl.Camellia.PPC64LE.ecb .decrypt)
    verified := Proof.Camellia.PPC64LE.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.PPC64LE
