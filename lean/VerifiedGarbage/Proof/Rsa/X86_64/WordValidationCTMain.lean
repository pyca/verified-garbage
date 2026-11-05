module
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTSetup
public import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationCT
public import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationMain

import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTLoads
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTSetup
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTLoads
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant time of CRT-key validation with a word remainder

The common setup and earlier checks retain `KK`. The adapter preserves
that context using the public workspace bounds established by setup.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

/-- `main` is constant time from `M0`. -/
theorem ckMainFast_ct : RelCT isa (Two M0) Impl.Rsa.X86_64.CheckCrtKey.mainFast fun _ _ => True := by
  rw [crtMainFast_eq]
  refine RelCT.seqs_append (by simp) (by simp [loadNum]) (RelCT.seq setupK_ct
    (RelCT.mono (P := Two KK) ?_ (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a.kp, h₁, h₂⟩) fun _ _ h => h))
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum])
    (RelCT.seq (kk_app (by simp [loadNum]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck]) (kk_app (by simp [loadNum])
      (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PX ld_QR)
      mulXRK_ct) eqCheckK_ct) ?_)
  refine RelCT.seqs_append (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum])
    (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (RelCT.seq
    (ckModChecks_ct (by decide) (by decide) (·.pl) (fun _ _ h => ⟨h.hPl, h.pl1, h.pl2⟩) ld_PM ld_DP
      (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (by simp)
    (RelCT.seq (ckModChecks_ct (by decide) (by decide) (·.ql) (fun _ _ h => ⟨h.hQl, h.ql1, h.ql2⟩) ld_QM ld_DQ
      (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq wordQInv_ct ?_)
  exact outK_ct

end VG.Proof.Rsa.X86_64.Key
