import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTSetup

/-!
# `vg_rsa_check_key` on x86-64: constant time of `main`

The setup (`setupK_ct`), then each check from `KK` (`KeyCTPieces.lean`),
then the result from `rdi` (`main_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

theorem kk_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) (h₁ : RelCT isa (Two KK) (seqs a) (Two KK))
    (h₂ : RelCT isa (Two KK) (seqs b) (Two KK)) : RelCT isa (Two KK) (seqs (a ++ b)) (Two KK) :=
  RelCT.seqs_append ha hb (RelCT.seq h₁ h₂)

theorem ld_D : RelCT isa (Two KK) (seqs (loadNum aX sD sDlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pd) (·.dl)
    (fun _ _ h => ⟨h.hD, h.hDl, h.srD, h.dl1, h.dl2⟩) (by taint_decide) (by taint_decide)

theorem ld_PX : RelCT isa (Two KK) (seqs (loadNum aX sP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pp) (·.pl)
    (fun _ _ h => ⟨h.hP, h.hPl, h.srP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_PM : RelCT isa (Two KK) (seqs (loadNum aM sP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pp) (·.pl)
    (fun _ _ h => ⟨h.hP, h.hPl, h.srP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_QR : RelCT isa (Two KK) (seqs (loadNum aR sQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pq) (·.ql)
    (fun _ _ h => ⟨h.hQ, h.hQl, h.srQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_QM : RelCT isa (Two KK) (seqs (loadNum aM sQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pq) (·.ql)
    (fun _ _ h => ⟨h.hQ, h.hQl, h.srQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_DP : RelCT isa (Two KK) (seqs (loadNum aX sDP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pdp) (·.pl)
    (fun _ _ h => ⟨h.hDP, h.hPl, h.srDP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_DQ : RelCT isa (Two KK) (seqs (loadNum aX sDQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pdq) (·.ql)
    (fun _ _ h => ⟨h.hDQ, h.hQl, h.srDQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_QI : RelCT isa (Two KK) (seqs (loadNum aX sQI sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pqi) (·.pl)
    (fun _ _ h => ⟨h.hQI, h.hPl, h.srQI, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ltXN : RelCT isa (Two KK) (seqs (ltMask aX aN)) (Two KK) := ltMaskK_ct (by decide) (by decide) (by taint_decide)

theorem ltXM : RelCT isa (Two KK) (seqs (ltMask aX aM)) (Two KK) := ltMaskK_ct (by decide) (by decide) (by taint_decide)

theorem modChecks_ct {sX sXlen sDX : Nat} (hM : RelCT isa (Two KK) (seqs (loadNum aM sX sXlen)) (Two KK))
    (hX : RelCT isa (Two KK) (seqs (loadNum aX sDX sXlen)) (Two KK)) :
    RelCT isa (Two KK) (seqs (modChecks sX sXlen sDX)) (Two KK) := by
  unfold modChecks
  refine kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [reduce])
    (kk_app (by simp [loadNum]) (by simp [mulE]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [reduce])
    (kk_app (by simp [loadNum]) (by simp [mulE]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [ltMask]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [decM]) hM decMK_ct) hX) ltXM) ld_D) mulEK_ct) reduceEK_ct) eqOneK_ct) hX)
    mulEK_ct) reduceEK_ct) eqOneK_ct

/-- The result, from `KK`. -/
theorem outK_ct : RelCT isa (Two KK)
    (.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)) fun _ _ => True :=
  two_taint [.rdi] pins_kk (by taint_decide)

/-- `main` is constant time from `M0`. -/
theorem main_ct : RelCT isa (Two M0) main fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp) (by simp [loadNum]) (RelCT.seq setupK_ct
    ((RelCT.seqs_append (by simp [loadNum]) (by simp [loadNum]) (RelCT.seq
      (kk_app (by simp [loadNum]) (by simp [ltMask]) ld_D ltXN) ?_)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a.kp, h₁, h₂⟩) fun _ _ h => h))
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [modChecks, loadNum]) (RelCT.seq
    (kk_app (by simp [loadNum]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck]) (kk_app (by simp [loadNum])
      (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PX ld_QR)
      mulXRK_ct) eqCheckK_ct) ?_)
  refine RelCT.seqs_append (by simp [modChecks, loadNum]) (by simp [modChecks, loadNum]) (RelCT.seq
    (modChecks_ct ld_PM ld_DP) ?_)
  refine RelCT.seqs_append (by simp [modChecks, loadNum]) (by simp [loadNum]) (RelCT.seq
    (modChecks_ct ld_QM ld_DQ) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp) (RelCT.seq
    (kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [reduce])
      (kk_app (by simp [loadNum]) (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) (kk_app (by simp [loadNum]) (by simp [ltMask])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PM ld_QI) ltXM) ld_QR) mulXRK_ct) reduceXRK_ct) eqOneK_ct)
    ?_)
  exact outK_ct

end VG.Proof.Rsa.X86_64
