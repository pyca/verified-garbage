module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Impl.AesOcb.X86_64.Fn
import VerifiedGarbage.Proof.AesOcb.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Impl.AesCcm.X86_64
import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Blocks
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesOcb.X86_64.Hash
import VerifiedGarbage.Proof.AesOcb.X86_64.HashFill
import VerifiedGarbage.Proof.AesOcb.X86_64.InitCT
import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
import VerifiedGarbage.Proof.AesOcb.X86_64.Offset0
import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
import VerifiedGarbage.Proof.Cmac.Dbl32
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
import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
import VerifiedGarbage.Proof.AesOcb.X86_64.Scrub
import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.Verified
import VerifiedGarbage.Proof.Variants.AesOcb.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OCB (RFC 7253) on x86-64 -/

namespace VG.Artifacts.AesOcb.X86_64

open VG.Proof.AesOcb.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.map (fun (v : Proof.Aes.X86_64.BlocksImpl) =>
    Spec.Ocb.initApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesOcb.X86_64.Fn.init v.level v.free.isSome (Proof.AesOcb.X86_64.callees v)
      verified := Proof.AesOcb.X86_64.Scrub.ocbInit_scrubbed v
      spSafe := Proof.AesOcb.X86_64.Scrub.ocbInit_spSafeFn v }) ++
  VG.Proof.Variants.AesOcb.X86_64.variants.flatMap fun (o : Proof.AesOcb.X86_64.OcbImpl) => [
    Spec.Ocb.sealApi.artifact X86_64.target
      (match o with
      | .onePass =>
        { suffix := "_aesni"
          code := Impl.AesOcb.X86_64.Fn.sealOnePass .sse
          verified := Proof.AesOcb.X86_64.AesNi.seal_scrubbed
          spSafe := Proof.AesOcb.X86_64.AesNi.seal_spSafeFn }
      | .blocks v =>
        { suffix := v.suffix
          code := Impl.AesOcb.X86_64.Fn.«seal» v.level (Proof.AesOcb.X86_64.callees v)
          verified := Proof.AesOcb.X86_64.Scrub.seal_scrubbed v
          spSafe := Proof.AesOcb.X86_64.Scrub.seal_spSafeFn v }),
    Spec.Ocb.openApi.artifact X86_64.target
      (match o with
      | .onePass =>
        { suffix := "_aesni"
          code := Impl.AesOcb.X86_64.Fn.openOnePass .sse
          verified := Proof.AesOcb.X86_64.AesNi.open_scrubbed
          spSafe := Proof.AesOcb.X86_64.AesNi.open_spSafeFn }
      | .blocks v =>
        { suffix := v.suffix
          code := Impl.AesOcb.X86_64.Fn.«open» v.level (Proof.AesOcb.X86_64.callees v)
          verified := Proof.AesOcb.X86_64.Scrub.open_scrubbed v
          spSafe := Proof.AesOcb.X86_64.Scrub.open_spSafeFn v })]

spec_apis artifacts

end VG.Artifacts.AesOcb.X86_64
