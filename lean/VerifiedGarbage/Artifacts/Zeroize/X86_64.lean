module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Zeroize.Contract
import VerifiedGarbage.Impl.Zeroize.X86_64.Fn
import VerifiedGarbage.Proof.Zeroize.X86_64Avx
import VerifiedGarbage.Proof.Zeroize.X86_64Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Zeroization on x86-64 -/

namespace VG.Artifacts.Zeroize.X86_64
open VG.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Zeroize.zeroizeApi.artifact target { code := Impl.Zeroize.X86_64.Fn.zeroize, verified := Proof.Zeroize.X86_64.zeroize_scrubbed, spSafe := Proof.Zeroize.X86_64.zeroize_spSafe },
  Spec.Zeroize.zeroizeApi.artifact target { suffix := "_avx", code := Impl.Zeroize.X86_64.Fn.zeroizeAvx, verified := Proof.Zeroize.X86_64.zeroizeAvx_scrubbed, spSafe := Proof.Zeroize.X86_64.zeroizeAvx_spSafe }]

spec_apis artifacts

end VG.Artifacts.Zeroize.X86_64
