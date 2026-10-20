module

public import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
public import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
public import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.ConstantTime
public import VerifiedGarbage.Proof.TripleDes.AArch64.Box
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Correct
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Permutation
public import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
public import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
public import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.ConstantTime
import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Correct
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Permutation
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Permutation

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
