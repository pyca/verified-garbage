module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-! The machine callees shared by the AES-GCM entry points. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64 (Calls)

/-- What the functions of `v` call, as `Impl/` takes it. -/
def GcmImpl.calls (v : GcmImpl) : Calls :=
  ⟨v.ctr.callee, v.ctr.to, v.key.fn, v.gh.fn, v.gh.pmull, v.stitch, v.suffix⟩

end VG.Proof.AesGcm.AArch64
