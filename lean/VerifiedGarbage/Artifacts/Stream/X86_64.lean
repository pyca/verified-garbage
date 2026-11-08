module

public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
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
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
public import VerifiedGarbage.Proof.Variants.Blake2s.X86_64
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # Streaming BLAKE2b on x86-64, for every compression backend -/

@[expose] public section

namespace VG.Artifacts.Stream.X86_64.Blake2b

def artifacts (v : Proof.Blake2.X86_64.Backend) : List Artifact := [
  Spec.Blake2.updateBApi.artifact VG.X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update
    stack := 8 + 584
    verified := v.update_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.updateSpSafe
    features := v.features },
  Spec.Blake2.finalizeBApi.artifact VG.X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize
    stack := 8 + 584
    verified := v.finalize_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.finalizeSpSafe
    features := v.features }]

end VG.Artifacts.Stream.X86_64.Blake2b

-- Streaming BLAKE2s on x86-64, for every compression backend
namespace VG.Artifacts.Stream.X86_64.Blake2s

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

end VG.Artifacts.Stream.X86_64.Blake2s

-- Streaming Merkle–Damgård hash functions on X86_64
namespace VG.Artifacts.Stream.X86_64.MdHash

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := v.stream.map fun f =>
  f.api.artifact X86_64.target { f.reg with suffix := v.suffix, features := v.features }

end VG.Artifacts.Stream.X86_64.MdHash

namespace VG.Artifacts.Stream.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.Blake2b.X86_64.variants.flatMap fun v => Blake2b.artifacts v) ++
  (VG.Proof.Variants.Blake2s.X86_64.variants.flatMap fun v => Blake2s.artifacts v) ++
  (VG.Proof.Variants.MdHash.X86_64.variants.flatMap fun v => MdHash.artifacts v)

end VG.Artifacts.Stream.X86_64
