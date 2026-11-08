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
public import VerifiedGarbage.TCB.AArch64.Print

@[expose] public section

namespace VG.Artifacts.TripleDes.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64 Impl.TripleDes.AArch64.Key.expandKey
    stack := 512
    verified := Proof.TripleDes.AArch64.expandKey_framed },
  Spec.TripleDes.ecbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1024 .x3 128
      Impl.TripleDes.AArch64.BitsliceNeon.encrypt
    stack := 1024
    verified := Proof.TripleDes.AArch64.ecb_framed Proof.TripleDes.AArch64.BitslicedNeon.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1024 .x3 128
      Impl.TripleDes.AArch64.BitsliceNeon.decrypt
    stack := 1024
    verified := Proof.TripleDes.AArch64.ecb_framed Proof.TripleDes.AArch64.BitslicedNeon.decrypt_verified }]

end VG.Artifacts.TripleDes.AArch64
