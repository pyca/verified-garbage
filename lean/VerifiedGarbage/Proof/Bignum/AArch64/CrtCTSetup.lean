import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupChk

/-!
# RSA with the CRT on AArch64: constant time of the setup and the checks

The claims of `CrtCTDefs.lean` for the primes' setup: the loads
(`loadArr_ct_pN`, `loadArr_ct_pI`, `loadArr_ct_qN`, in `CrtCTSetupLoad.lean`),
`primesSetup` (`setup_ct`, in `CrtCTSetupWs.lean`), and `checks`
(`checks_ct`), from its pieces (`CrtCTSetupChk.lean`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem leaveEnterQ_ck : RelCT isa (Two (CKr ckP)) (.block [leave, enterQ]) (Two (CKr ckQ)) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (RelCT.seq (two_piece (Ψ := CKr (·.B)) [.x0] (pins_ckr _) (by taint_decide) fun p s h => leaveP_ck h)
      (two_piece [.x0] (pins_ckr _) (by taint_decide) fun p s h => enterQ_ck h))

theorem checks_ct : ChecksCT := by
  unfold ChecksCT checks
  simp only [List.append_assoc]
  refine two_map id (fun _ _ h => h.ck) ?_
  refine RelCT.seqs_append (by simp [pqProduct, zeroAccs]) (by simp [eqCheck]) (RelCT.seq pq_ct ?_)
  refine RelCT.seqs_append (by simp [eqCheck]) (by simp) (RelCT.seq eq_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [qinvCheck]) (RelCT.seq (two_piece [.x0] (pins_ckr _)
    (by taint_decide) fun p s h => enterP_ck h) ?_)
  refine RelCT.seqs_append (by simp [qinvCheck]) (by simp [primeFix]) (RelCT.seq qinv_ct ?_)
  refine RelCT.seqs_append (by simp [primeFix]) (by simp) (RelCT.seq fixP_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [primeFix]) (RelCT.seq leaveEnterQ_ck ?_)
  refine RelCT.seqs_append (by simp [primeFix]) (by simp) (RelCT.seq fixQ_ct ?_)
  exact two_taint [.x0] (pins_ckr _) (by taint_decide)

end VG.Proof.Bignum.AArch64
