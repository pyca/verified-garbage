module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Impl.AesCcm.X86_64.Fn
import VerifiedGarbage.Proof.AesCcm.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs
import VerifiedGarbage.Proof.AesCcm.X86_64.Header
import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.OpenCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
import VerifiedGarbage.Proof.AesCcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.Variants.CmacAesUpdate.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CCM (NIST SP 800-38C) on x86-64 -/

namespace VG.Artifacts.AesCcm.X86_64

open VG.Proof.AesCcm.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.CmacAesUpdate.X86_64.variants.flatMap fun (v : Proof.CmacAes.X86_64.UpdateImpl) => [
    Spec.Ccm.sealApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCcm.X86_64.Fn.«seal» (v.level.join v.ctr.level) v.callee v.ctr.callee
      verified := Proof.AesCcm.X86_64.seal_scrubbed v
      spSafe := Proof.AesCcm.X86_64.seal_spSafeFn v },
    Spec.Ccm.openApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCcm.X86_64.Fn.«open» (v.level.join v.ctr.level) v.callee v.ctr.callee
      verified := Proof.AesCcm.X86_64.open_scrubbed v
      spSafe := Proof.AesCcm.X86_64.open_spSafeFn v }]

spec_apis artifacts

end VG.Artifacts.AesCcm.X86_64
