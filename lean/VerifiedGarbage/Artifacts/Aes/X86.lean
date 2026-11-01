module
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant

public import VerifiedGarbage.Proof.Aes.X86.Ctr32
public import VerifiedGarbage.Proof.Aes.X86.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
public import VerifiedGarbage.Proof.Aes.X86.BlocksCT
public import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain
public import VerifiedGarbage.Proof.Aes.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Body
public import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
public import VerifiedGarbage.Proof.Aes.X86.Blocks
public import VerifiedGarbage.Proof.Aes.X86.Decrypt
public import VerifiedGarbage.Proof.Aes.X86.Keys
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
import VerifiedGarbage.Proof.Aes.X86.AesNi.Body
import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost
import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
import VerifiedGarbage.Proof.Aes.X86.Blocks
import VerifiedGarbage.Proof.Aes.X86.Decrypt
import VerifiedGarbage.Proof.Aes.X86.Keys
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/-! # AES on x86 -/

@[expose] public section

namespace VG.Artifacts.Aes.X86

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey
    stack := 532
    verified := Proof.Aes.X86.scalar_expandKey_framed },
  Spec.Aes.expandKeyApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey
    stack := 532
    verified := Proof.Aes.X86.aesni_expandKey_framed
    features := ["aes"] },
  Spec.Aes.encryptBlocksApi.artifact X86.target {
    code := Impl.Aes.X86.encryptBlocks
    verified := Proof.Aes.X86.encryptBlocks_verified },
  Spec.Aes.decryptBlocksApi.artifact X86.target {
    code := Impl.Aes.X86.decryptBlocks
    verified := Proof.Aes.X86.decryptBlocks_verified },
  Spec.Aes.encryptBlocksApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Aes.X86.AesNi.encryptBlocks
    verified := Proof.Aes.X86.AesNi.encryptBlocks_verified
    features := ["aes"] },
  Spec.Aes.decryptBlocksApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Aes.X86.AesNi.decryptBlocks
    verified := Proof.Aes.X86.AesNi.decryptBlocks_verified
    features := ["aes"] }]

end VG.Artifacts.Aes.X86
