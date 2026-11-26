module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Impl.Blake2.X86_64.Fn
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blake2.X86_64.Backend
import VerifiedGarbage.Proof.Blake2.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
import VerifiedGarbage.Proof.Variants.Blake2s.X86_64
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2b (RFC 7693) on x86-64 -/

namespace VG.Artifacts.Blake2b.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Blake2.initBApi.artifact X86_64.target { code := Impl.Blake2.X86_64.Fn.initB, verified := Proof.Blake2.X86_64.initB_scrubbed, spSafe := Proof.Blake2.X86_64.initB_spSafe }] ++
  (VG.Proof.Variants.Blake2b.X86_64.variants.flatMap fun (v : Proof.Blake2.X86_64.Backend) => [
    Spec.Blake2.updateBApi.artifact VG.X86_64.target {
      suffix := v.suffix
      notWith := v.notWith
      code := Impl.Blake2.X86_64.Fn.update Spec.Blake2.b v.updScrub.level v.updScrub.runs v.hashCallee
      verified := Proof.Blake2.X86_64.updateB_scrubbed v
      spSafe := Proof.Blake2.X86_64.updateB_spSafe v },
    Spec.Blake2.finalizeBApi.artifact VG.X86_64.target {
      suffix := v.suffix
      notWith := v.notWith
      code := Impl.Blake2.X86_64.Fn.finalize Spec.Blake2.b v.finScrub.level v.finScrub.runs v.hashCallee
      verified := Proof.Blake2.X86_64.finalizeB_scrubbed v
      spSafe := Proof.Blake2.X86_64.finalizeB_spSafe v }])

spec_apis artifacts

end VG.Artifacts.Blake2b.X86_64
