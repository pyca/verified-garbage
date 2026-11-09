module

public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Blake2.Spec
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
public import VerifiedGarbage.Proof.Variants.Blake2s.X86_64
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # BLAKE2s (RFC 7693) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.X86_64

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact X86_64.target {
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.s
    verified := Proof.Blake2.X86_64.Stream.initS_verified }] ++
  (VG.Proof.Variants.Blake2s.X86_64.variants.flatMap fun (v : Proof.Blake2.X86_64.BackendS) => [
    Spec.Blake2.updateSApi.artifact VG.X86_64.target {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update
      stack := 8 + 584
      verified := v.update_framed
      spSafe := X86_64.withStackScratch_spSafe_of v.updateSpSafe
      features := v.features },
    Spec.Blake2.finalizeSApi.artifact VG.X86_64.target {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize
      stack := 8 + 584
      verified := v.finalize_framed
      spSafe := X86_64.withStackScratch_spSafe_of v.finalizeSpSafe
      features := v.features }])

end VG.Artifacts.Blake2s.X86_64
