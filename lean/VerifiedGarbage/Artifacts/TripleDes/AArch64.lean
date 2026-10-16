module

public import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.AArch64.Frame
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.TripleDes.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64 scalar key expansion with fixed permutations and public round-count branches."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64 Impl.TripleDes.AArch64.Key.expandKey
    stack := 512
    verified := Proof.TripleDes.AArch64.expandKey_framed },
  Spec.TripleDes.encryptBlockApi.artifact AArch64.target {
    notes := ["Baseline AArch64 scalar Boolean S-box circuits; IP and FP shared across all three DES passes."]
    code := Impl.TripleDes.AArch64.encryptBlock
    stack := 0
    verified := Proof.TripleDes.AArch64.encrypt_verified },
  Spec.TripleDes.decryptBlockApi.artifact AArch64.target {
    notes := ["Baseline AArch64 scalar Boolean S-box circuits with reverse EDE key order."]
    code := Impl.TripleDes.AArch64.decryptBlock
    stack := 0
    verified := Proof.TripleDes.AArch64.decrypt_verified },
  Spec.TripleDes.ecbEncryptApi.artifact AArch64.target {
    notes := ["Bitsliced in AdvSIMD registers: 128 blocks at a time, in place in the data, in 128-bit words, through Boolean S-box circuits; the blocks left after the last 128 through the scratch buffer."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1024 .x3 128
      Impl.TripleDes.AArch64.BitsliceNeon.encrypt
    stack := 1024
    verified := Proof.TripleDes.AArch64.ecb_framed Proof.TripleDes.AArch64.BitslicedNeon.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact AArch64.target {
    notes := ["Bitsliced in AdvSIMD registers: 128 blocks at a time, in place in the data, in 128-bit words, through Boolean S-box circuits; the blocks left after the last 128 through the scratch buffer."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1024 .x3 128
      Impl.TripleDes.AArch64.BitsliceNeon.decrypt
    stack := 1024
    verified := Proof.TripleDes.AArch64.ecb_framed Proof.TripleDes.AArch64.BitslicedNeon.decrypt_verified }]

end VG.Artifacts.TripleDes.AArch64
