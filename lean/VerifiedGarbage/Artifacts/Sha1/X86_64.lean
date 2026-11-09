module

public import VerifiedGarbage.Proof.Sha1.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
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
public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
public import VerifiedGarbage.Proof.Variants.Blake2s.X86_64
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # SHA-1 (FIPS 180-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha1.X86_64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact X86_64.target {
    code := Impl.Sha1.X86_64.Stream.init
    verified := Proof.Sha1.X86_64.Shared.init }] ++
  (VG.Proof.Variants.MdHash.X86_64.sha1Variants.flatMap fun (v : Proof.Pbkdf2.Md.X86_64.MdHash) =>
    v.stream.map fun f =>
      f.api.artifact X86_64.target { f.reg with suffix := v.suffix})

end VG.Artifacts.Sha1.X86_64
