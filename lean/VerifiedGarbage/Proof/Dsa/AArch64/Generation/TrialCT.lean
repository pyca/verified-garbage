module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial

/-! Reuse RSA's trial-division timing proof with the smaller DSA workspace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem nativeTrialHead_ok {q : VG.Proof.RsaKeyGen.AArch64.FPub} {s : State} (hw : VG.Proof.Rsa.AArch64.Ws s q.B q.Z q.w)
    (hT : slot q.w aTab + 2048 ≤ q.Z) :
    WP isa (.block (ws ++ base aTab .x9 ++ tabWrite ++ [movi .x3 128, movi .x4 256, movi .x5 17,
      .subs .x .x6 .x12 .x5, .csel .x .x10 .x4 .x3, movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1])) s fun t =>
      0 < trN q ∧ TI q 0 t := by
  have hn := hw.scr.nowrap
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨⟨h12₁, h11₁, hm₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aTab .x9 ((k₁.gpr .x0 (by decide)).trans hw.x0) h11₁)
    fun s₂ ⟨⟨h9₂, hm₂, _⟩, k₂⟩ => ?_
  refine WP.mono (tabWrites_ok (hw.scr.congr (k₁.trans k₂).wr) hT h9₂ 256 (Nat.le_refl _))
    fun s₃ ⟨htab₃, ho₃, k₃⟩ => ?_
  rw [hm₂, hm₁] at ho₃
  have h12₃ : s₃.gpr .x12 = BitVec.ofNat 64 q.w :=
    (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12₁)
  refine WP.mono (trialInit_ok s₃ h12₃ hw.w2) fun s₄ ⟨⟨h10₄, h1₄, h7₄, h8₄, hm₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hf₄ : Frm q.B [(slot q.w aTab, 2048)] s.mem s₄.mem := by rw [hm₄]; exact Frm.of_outside ho₃ (by simp)
  refine ⟨(trN_le q).2, hw.congr' hf₄ (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k14
    (by decide), hT, by rw [k₄.gpr .x9 (by decide), k₃.gpr .x9 (by decide), h9₂, Nat.mul_zero, Nat.add_zero],
    by rw [h10₄, Nat.sub_zero]; rfl, h7₄, h8₄, fun i hi => by rw [hm₄]; exact htab₃ i hi,
    by rw [h1₄, Nat.mul_zero, anyPre_zero]; rfl⟩

/-- Trial division needs the table's actual bound, without RSA keygen's larger arena. -/
theorem trial_ws_ct :
    RelCT isa (Two fun (q : VG.Proof.RsaKeyGen.AArch64.FPub) s => VG.Proof.Rsa.AArch64.Ws s q.B q.Z q.w ∧
      slot q.w aTab + 2048 ≤ q.Z) (seqs trial) (fun _ _ => True) := by
  have hh := fun (q : VG.Proof.RsaKeyGen.AArch64.FPub) s (h : VG.Proof.Rsa.AArch64.Ws s q.B q.Z q.w ∧ slot q.w aTab + 2048 ≤ q.Z) =>
    nativeTrialHead_ok h.1 h.2
  simp only [List.append_assoc] at hh
  simp only [trial, seqs, List.append_assoc]
  refine RelCT.seq (two_post (ws_block_ct0 VG.Proof.RsaKeyGen.AArch64.FPub.B VG.Proof.RsaKeyGen.AArch64.FPub.Z VG.Proof.RsaKeyGen.AArch64.FPub.w (fun _ _ h => h.1) (by taint_decide)) hh)
    ((two_loop (Φ := TI) (Ψ := fun _ _ => True) trN trialBody_ct fun _ _ _ hk h => trialIter_ok hk h).mono
      (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.Dsa.AArch64.Generation
