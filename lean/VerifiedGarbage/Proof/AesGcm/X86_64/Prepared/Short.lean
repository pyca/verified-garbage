import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified

/-! # Prepared contexts retain the existing short-message path -/
namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared)

theorem sealSelPrepared_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk B)))
      (Spec.Gcm.sealPreparedContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCode; split
  · exact sealPreparedCode_framed (sealPreparedCode_verified (Short.sealM_correct v B hF) (Short.sealM_ct hF v B))
      (Short.sealM_spSafe v B) (Short.sealM_xdepth v B)
  · exact sealPrepared_framed v B

/-- `vg_aes_gcm_open_prepared`, with the short path if `v` has it. -/
theorem openSelPrepared_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode (v.withBlk B)))
      (Spec.Gcm.openPreparedContract X86_64.abi 2632) := by
  unfold GcmImpl.openCode; split
  · exact openPreparedCode_framed (openPreparedCode_verified (Short.openM_correct v B hF) (Short.openM_ct hF v B))
      (Short.openM_spSafe v B) (Short.openM_xdepth v B)
  · exact openPrepared_framed v B

end VG.Proof.AesGcm.X86_64
