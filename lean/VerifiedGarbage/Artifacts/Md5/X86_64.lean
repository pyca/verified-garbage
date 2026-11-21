module

public import VerifiedGarbage.Impl.Md5.X86_64.Fn
public import VerifiedGarbage.Proof.Md5.X86_64.Shared
public import VerifiedGarbage.Proof.Md5.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Md5.X86_64.Lit
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

/-! # MD5 (RFC 1321) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Md5.X86_64

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact X86_64.target { code := Impl.Md5.X86_64.Fn.init, verified := Proof.Md5.X86_64.init_scrubbed, spSafe := Proof.Md5.X86_64.init_spSafe },
  Spec.Md5.updateApi.artifact X86_64.target { code := Impl.Md5.X86_64.Fn.update, verified := Proof.Md5.X86_64.update_scrubbed, spSafe := Proof.Md5.X86_64.update_spSafe },
  Spec.Md5.finalizeApi.artifact X86_64.target { code := Impl.Md5.X86_64.Fn.finalize, verified := Proof.Md5.X86_64.finalize_scrubbed, spSafe := Proof.Md5.X86_64.finalize_spSafe }]

end VG.Artifacts.Md5.X86_64
