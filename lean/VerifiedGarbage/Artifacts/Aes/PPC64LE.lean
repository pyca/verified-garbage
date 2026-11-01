module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Aes.PPC64LE

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.expandKey
    verified := Proof.Aes.PPC64LE.expandKey_direct_verified },
  Spec.Aes.encryptBlocksApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.encryptBlocks
    verified := Proof.Aes.PPC64LE.encryptBlocks_verified },
  Spec.Aes.decryptBlocksApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.decryptBlocks
    verified := Proof.Aes.PPC64LE.decryptBlocks_verified }]

end VG.Artifacts.Aes.PPC64LE
