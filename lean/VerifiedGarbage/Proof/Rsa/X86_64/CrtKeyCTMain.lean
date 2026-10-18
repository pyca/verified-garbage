module

public import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
public import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_check_crt_key` on x86-64: constant time of `main`

`reduceTop` from `KK` (`reduceTopK_ct`): its header loads from `rdi`, the
rest from the registers they pin, which are public (`w'` and `c` from the
lengths); then `main` as `vg_rsa_check_key`'s (`ckMain_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

/-- `main` is constant time from `M0`. -/
theorem ckMain_ct : RelCT isa (Two M0) Impl.Rsa.X86_64.CheckCrtKey.main fun _ _ => True := by
  rw [crtMain_eq]
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
  refine RelCT.seqs_append (by simp [Impl.Rsa.X86_64.CheckCrtKey.modChecks, loadNum]) (by simp [loadNum])
    (RelCT.seq (ckModChecks_ct (by decide) (by decide) (·.ql) (fun _ _ h => ⟨h.hQl, h.ql1, h.ql2⟩) ld_QM ld_DQ
      (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp) (RelCT.seq
    (kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum])
      (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
      (kk_app (by simp [loadNum]) (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) (kk_app (by simp [loadNum]) (by simp [ltMask])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PM ld_QI) ltXM) ld_QR) mulXRK_ct) reduceTopQK_ct)
      eqOneK_ct)
    ?_)
  exact outK_ct

end VG.Proof.Rsa.X86_64.Key
