module

public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
public import VerifiedGarbage.Proof.Blake2.X86_64.Scrub
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

/-! # BLAKE2b (RFC 7693) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.X86_64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact X86_64.target Proof.Blake2.X86_64.initBReg] ++
  (VG.Proof.Variants.Blake2b.X86_64.variants.flatMap fun (v : Proof.Blake2.X86_64.Backend) => [
    Spec.Blake2.updateBApi.artifact VG.X86_64.target (Proof.Blake2.X86_64.updateBReg v),
    Spec.Blake2.finalizeBApi.artifact VG.X86_64.target (Proof.Blake2.X86_64.finalizeBReg v)])

end VG.Artifacts.Blake2b.X86_64
