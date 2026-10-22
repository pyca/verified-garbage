module

public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.VerifiedP
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.SealSel
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA

/-! # Sixteen prepared powers: `seal` and `open` without the short path

`Prepared/Short.lean`'s `sealSelPrepared_framed` and `openSelPrepared_framed`
for a key context of `vg_aes_gcm_prepare16`, for implementations without the
short path (`hs`), whose table of powers is copied from all 48: `SealFin` and
`FastOpen.openFin` around the path for TLS records, at every length. -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
variable (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8))

theorem sealSelPrepared16_framed (hF : Short.ShortFacts) (hs : v.short = false) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCodeP (v.withBlk B)))
      (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624) := by
  unfold GcmImpl.sealCodeP; rw [if_neg (by rw [hs]; decide)]; split
  · exact sealPrepared16Code_framed (sealPrepared16Code_verified (Short.sealFinP_correct v B hF)
      (SealFin.sealFMW_ct v B (FastSeal.sealSel_ok hF v B Short.finKsA_ksOk (SealFin.sealLongOk_mid v B hF))
        (FastSeal.sealSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel (SealFin.sealLongRel_mid v B hF))))
      (Short.sealFinP_spSafe v B) (Short.sealFinP_xdepth v B)
  · exact sealPrepared16_framed v B

/-- `vg_aes_gcm_open_prepared16`, for implementations without the short path. -/
theorem openSelPrepared16_framed (hF : Short.ShortFacts) (hs : v.short = false) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCodeP (v.withBlk B)))
      (Spec.Gcm.openPrepared16Contract X86_64.abi 2632) := by
  unfold GcmImpl.openCodeP; rw [if_neg (by rw [hs]; decide)]
  exact openPrepared16Code_framed (openPrepared16Code_verified (Short.openFinP_correct v B hF)
    (FastOpen.openFinW_ct (FastOpen.openSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel
      (Short.longRel_openLong v B)))) (Short.openFinP_spSafe v B) (Short.openFinP_xdepth v B)

end VG.Proof.AesGcm.X86_64
