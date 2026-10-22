module

public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.VerifiedP
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.PowP
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.SealSel
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.KsA

/-! # Sixteen prepared powers: Prepared contexts: the short path with the context's powers

`vg_aes_gcm_seal_prepared` and `vg_aes_gcm_open_prepared` take the short
path with its table of powers copied from the prepared key context
(`GcmImpl.sealCodeP`, `GcmImpl.openCodeP`), and otherwise the code of the
other instances, which `seal` and `open` replace for TLS records with
`FastSeal.sel` and `FastOpen.sel`. -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
variable (v : GcmImpl) (B : BlkFn (CtxMode.preparedN 8))

theorem sealSelPrepared16_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCodeP (v.withBlk B)))
      (Spec.Gcm.sealPrepared16Contract X86_64.abi 2624) := by
  unfold GcmImpl.sealCodeP; split
  · exact sealPreparedCode_framed (sealPreparedCode_verified (Short.sealMP_correct v B hF)
      (Short.sealMW_ct hF v B Short.powOk_powersP Short.powersP_ct
        (FastSeal.sealSel_ok hF v B Short.finKs_ksOk (Short.sealLongOk_sealLong hF v B))
        (FastSeal.sealSel_rel hF v B Short.finKs_ksOk Short.finKs_rel (Short.sealLongRel_sealLong hF v B)))) (Short.sealMP_spSafe v B)
      (Short.sealMP_xdepth v B)
  · split
    · exact sealPreparedCode_framed (sealPreparedCode_verified (Short.sealFinP_correct v B hF)
        (SealFin.sealFMW_ct v B (FastSeal.sealSel_ok hF v B Short.finKsA_ksOk (SealFin.sealLongOk_mid v B hF))
          (FastSeal.sealSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel (SealFin.sealLongRel_mid v B hF))))
        (Short.sealFinP_spSafe v B) (Short.sealFinP_xdepth v B)
    · exact sealPrepared16_framed v B

/-- `vg_aes_gcm_open_prepared`, with the short path if `v` has it. -/
theorem openSelPrepared16_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCodeP (v.withBlk B)))
      (Spec.Gcm.openPrepared16Contract X86_64.abi 2632) := by
  unfold GcmImpl.openCodeP; split
  · exact openPreparedCode_framed (openPreparedCode_verified (Short.openMP_correct v B hF)
      (Short.openMW_ct hF v B Short.powOk_powersP Short.powersP_ct
        (FastOpen.openSel_rel hF v B Short.finKs_ksOk Short.finKs_rel (Short.longRel_openLong v B)))) (Short.openMP_spSafe v B)
      (Short.openMP_xdepth v B)
  · exact openPreparedCode_framed (openPreparedCode_verified (Short.openFinP_correct v B hF)
      (FastOpen.openFinW_ct (FastOpen.openSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel
        (Short.longRel_openLong v B)))) (Short.openFinP_spSafe v B) (Short.openFinP_xdepth v B)

end VG.Proof.AesGcm.X86_64
