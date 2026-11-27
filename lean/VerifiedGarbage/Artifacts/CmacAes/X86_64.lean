module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Impl.CmacAes.Stream.X86_64.Fn
import VerifiedGarbage.Proof.CmacAes.X86_64.AesNi
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Frame
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64
import VerifiedGarbage.Proof.Variants.CmacAesUpdate.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CMAC (NIST SP 800-38B) on x86-64 -/

namespace VG.Artifacts.CmacAes.X86_64

open VG.Proof.CmacAes.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  (VG.Proof.Variants.CmacAesUpdate.X86_64.variants.flatMap fun (v : Proof.CmacAes.X86_64.UpdateImpl) => [
    Spec.Cmac.aesAbsorbApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86_64.Fn.absorb v.level v.space v.callee
      verified := Proof.CmacAes.Stream.X86_64.Scrub.absorb_scrubbed v
      spSafe := Proof.CmacAes.Stream.X86_64.Scrub.absorb_spSafeFn v }]) ++
  (VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.Ctr32Impl) => [
    Spec.Cmac.aesInitApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86_64.Fn.init v.level v.space v.expand v.callee v.suffix
      verified := Proof.CmacAes.Stream.X86_64.Scrub.init_scrubbed v
      spSafe := Proof.CmacAes.Stream.X86_64.Scrub.init_spSafeFn v },
    Spec.Cmac.aesFinishApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86_64.Fn.finish v.level v.space v.callee v.suffix
      verified := Proof.CmacAes.Stream.X86_64.Scrub.finish_scrubbed v
      spSafe := Proof.CmacAes.Stream.X86_64.Scrub.finish_spSafeFn v }])

spec_apis artifacts

end VG.Artifacts.CmacAes.X86_64
