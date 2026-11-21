module

public import VerifiedGarbage.Impl.Zeroize.X86_64.Fn
public import VerifiedGarbage.Proof.Zeroize.X86_64Avx
public import VerifiedGarbage.Proof.Zeroize.X86_64Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Zeroization on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Zeroize.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target { code := Impl.Zeroize.X86_64.Fn.zeroize, verified := Proof.Zeroize.X86_64.zeroize_scrubbed, spSafe := Proof.Zeroize.X86_64.zeroize_spSafe },
  Spec.Zeroize.zeroizeApi.artifact target { suffix := "_avx", code := Impl.Zeroize.X86_64.Fn.zeroizeAvx, verified := Proof.Zeroize.X86_64.zeroizeAvx_scrubbed, spSafe := Proof.Zeroize.X86_64.zeroizeAvx_spSafe }]
end VG.Artifacts.Zeroize.X86_64
