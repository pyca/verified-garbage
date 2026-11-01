module

public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
public import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Blocks
public import VerifiedGarbage.Proof.Aes.X86_64.Frame
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
public import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Gcm.Spec

/-! # AES on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Aes.X86_64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.Aes.X86_64.expandKey
    stack := 520
    verified := Proof.Aes.X86_64.scalar_expandKey_framed },
  Spec.Aes.expandKeyApi.artifact X86_64.target {
    suffix := "_aesni"
    code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64
      Impl.Aes.X86_64.AesNi.expandKey
    stack := 520
    verified := Proof.Aes.X86_64.aesni_expandKey_framed
    features := ["aes"] },
  Spec.Aes.encryptBlocksApi.artifact X86_64.target {
    code := Impl.Aes.X86_64.encryptBlocks
    verified := Proof.Aes.X86_64.encryptBlocks_verified },
  Spec.Aes.decryptBlocksApi.artifact X86_64.target {
    code := Impl.Aes.X86_64.decryptBlocks
    verified := Proof.Aes.X86_64.decryptBlocks_verified },
  Spec.Aes.encryptBlocksApi.artifact X86_64.target {
    suffix := "_aesni"
    written := [("scratch", 0)]
    code := Impl.Aes.X86_64.AesNi.encryptBlocks
    verified := Proof.Aes.X86_64.AesNi.encryptBlocks_verified
    writtenOk := Proof.Aes.X86_64.AesNi.encryptBlocks_written
    features := ["aes"] },
  Spec.Aes.decryptBlocksApi.artifact X86_64.target {
    suffix := "_aesni"
    code := Impl.Aes.X86_64.AesNi.decryptBlocks
    verified := Proof.Aes.X86_64.AesNi.decryptBlocks_verified
    features := ["aes"] },
  Spec.Aes.encryptBlocksApi.artifact X86_64.target {
    suffix := "_vaes"
    written := [("scratch", 0)]
    code := Impl.Aes.X86_64.VaesBlocks.encryptBlocks
    verified := Proof.Aes.X86_64.VaesBlocks.encryptBlocks_verified
    writtenOk := Proof.Aes.X86_64.VaesBlocks.encryptBlocks_written
    features := ["aes", "avx", "avx2", "vaes"] },
  Spec.Aes.decryptBlocksApi.artifact X86_64.target {
    suffix := "_vaes"
    code := Impl.Aes.X86_64.VaesBlocks.decryptBlocks
    verified := Proof.Aes.X86_64.VaesBlocks.decryptBlocks_verified
    features := ["aes", "avx", "avx2", "vaes"] }]

end VG.Artifacts.Aes.X86_64
