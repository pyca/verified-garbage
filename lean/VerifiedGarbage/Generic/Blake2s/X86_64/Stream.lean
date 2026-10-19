module

public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Registration

/-!
# Streaming BLAKE2s on x86-64, for every compression backend

The reviewed APIs supply signatures and contracts. Names carry the backend's
suffix, and every streaming caller calls that backend's compression function.
Initialization is backend-independent and stays in the registration file.
-/

@[expose] public section

namespace VG.Generic.Blake2s.X86_64.Stream

def artifacts (v : Proof.Blake2.X86_64.BackendS) : List Artifact := [
  Spec.Blake2.compressSApi.artifact VG.X86_64.target {
    suffix := v.suffix
    code := v.code
    verified := v.verified
    spSafe := v.spSafe
    features := v.features },
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
