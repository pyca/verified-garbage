module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Impl.Md5.X86_64.Fn
import VerifiedGarbage.Proof.Md5.X86_64.Shared
import VerifiedGarbage.Proof.Md5.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Md5.X86_64.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Backend
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
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
import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
import VerifiedGarbage.Proof.Variants.Blake2s.X86_64
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # MD5 (RFC 1321) on x86-64 -/

namespace VG.Artifacts.Md5.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Md5.initApi.artifact X86_64.target { code := Impl.Md5.X86_64.Fn.init, verified := Proof.Md5.X86_64.init_scrubbed, spSafe := Proof.Md5.X86_64.init_spSafe },
  Spec.Md5.updateApi.artifact X86_64.target { code := Impl.Md5.X86_64.Fn.update, verified := Proof.Md5.X86_64.update_scrubbed, spSafe := Proof.Md5.X86_64.update_spSafe },
  Spec.Md5.finalizeApi.artifact X86_64.target { code := Impl.Md5.X86_64.Fn.finalize, verified := Proof.Md5.X86_64.finalize_scrubbed, spSafe := Proof.Md5.X86_64.finalize_spSafe }]

spec_apis artifacts

end VG.Artifacts.Md5.X86_64
