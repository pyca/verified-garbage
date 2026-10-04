import VerifiedGarbage.Proof.Blake2.X86_64.BackendS

/-!
# Streaming BLAKE2s on x86-64, for every compression backend

The reviewed APIs supply signatures and contracts. Names carry the backend's
suffix, and every streaming caller calls that backend's compression function.
Initialization is backend-independent and stays in the registration file.
-/

namespace VG.Generic.Blake2s.X86_64.Stream

def artifacts (v : Proof.Blake2.X86_64.BackendS) : List Artifact := [
  { Spec.Blake2.compressSApi with
    name := v.compressName
    target := VG.X86_64.target
    doc := Spec.Blake2.compressSApi.doc
    code := v.code
    contract := Spec.Blake2.compressSContract VG.X86_64.abi
    verified := v.verified
    spSafe := v.spSafe
    features := v.features },
  { Spec.Blake2.updateSApi with
    name := Spec.Blake2.updateSApi.name ++ v.suffix
    target := VG.X86_64.target
    doc := Spec.Blake2.updateSApi.doc
    code := Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update
    contract := Spec.Blake2.updateSContract VG.X86_64.abi (8 + 584)
    stack := 8 + 584
    verified := v.update_framed
    spSafe := VG.X86_64.withStackScratch_spSafe (by decide) v.updateSpSafe
    features := v.features },
  { Spec.Blake2.finalizeSApi with
    name := Spec.Blake2.finalizeSApi.name ++ v.suffix
    target := VG.X86_64.target
    doc := Spec.Blake2.finalizeSApi.doc
    code := Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize
    contract := Spec.Blake2.finalizeSContract VG.X86_64.abi (8 + 584)
    stack := 8 + 584
    verified := v.finalize_framed
    spSafe := VG.X86_64.withStackScratch_spSafe (by decide) v.finalizeSpSafe
    features := v.features }]

end VG.Generic.Blake2s.X86_64.Stream
