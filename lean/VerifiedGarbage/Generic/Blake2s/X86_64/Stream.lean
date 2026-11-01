module

public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Blake2.Spec
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha256.Stream

/-! # Streaming BLAKE2s on x86-64, for every compression backend -/

@[expose] public section

namespace VG.Generic.Blake2s.X86_64.Stream

def artifacts (v : Proof.Blake2.X86_64.BackendS) : List Artifact := [
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
    features := v.features }]

end VG.Generic.Blake2s.X86_64.Stream
