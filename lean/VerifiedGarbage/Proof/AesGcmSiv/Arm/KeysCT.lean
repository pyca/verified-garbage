import VerifiedGarbage.Proof.AesGcmSiv.Arm.CTBase

/-!
# AES-GCM-SIV on ARMv7: the keys are constant time

Untrusted: everything here is checked by Lean. Both runs derive the same
number of blocks (`rounds / 2 − 1`, from `r8`); the code around the calls
passes the taint analysis, and each call has the same arguments in both
runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Proof.AesGcm.Arm (CtrCall ctr_call KeyCall key_call eval_ne')

/-- A run of `derive` before block `i`. -/
structure DC (p : Prm) (i : Nat) (t : State) : Prop where
  env : Env p t
  r4 : t.gpr .r4 = BitVec.ofNat 32 i

theorem derA_wp {p : Prm} (L : Lay p) {i : Nat} {t : State} (h : DC p i t) :
    WP isa (.block deriveBlock) t fun t₁ =>
      CtrCall t₁ p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 224) (p.W + BitVec.ofNat 32 2048) p.R 1 ∧
        DC p i t₁ := by
  obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := derArgs_ok L h.env h.r4
  have E₁ : Env p t₁ := h.env.of_others ho₁ sp₁ rd₁ wr₁
  exact WP.of_runBlock ⟨t₁, run₁, derCall L E₁ r0 r1 r2 r3 r12 lr, E₁, by rw [ho₁ _ (by decide), h.r4]⟩

theorem derC_wp {p : Prm} {i : Nat} {t : State}
    (h : CtrCall t p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 224) (p.W + BitVec.ofNat 32 2048) p.R 1 ∧
      DC p i t) :
    WP isa Impl.AesGcm.Arm.ctrFrame t (DC p i) :=
  WP.mono (ctr_call h.1) fun _ P =>
    ⟨h.2.env.of_saved P.saved P.sp P.rd P.wr, by rw [P.saved _ (by decide) (by decide), h.2.r4]⟩

theorem derP_wp {p : Prm} (L : Lay p) {i : Nat} (hi : i < p.R / 2 - 1) {t : State} (h : DC p i t) :
    WP isa (.block derivePost) t fun t' => DC p (i + 1) t' ∧ t'.z = decide (i + 1 = p.R / 2 - 1) := by
  obtain ⟨t', run', -, r4', z', ho', sp', rd', wr'⟩ := derPost_ok L h.env hi h.r4
  exact WP.of_runBlock ⟨t', run', ⟨h.env.of_others ho' sp' rd' wr', r4'⟩, z'⟩

theorem derA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4])) (.block deriveBlock) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem derP_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4])) (.block derivePost) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem der0_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [.mov .r4 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

/-- `derive`, in two runs with the same public arguments. -/
theorem derive_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) derive TT := by
  have hR := L.rounds
  have w0 : ∀ {σ : State}, Env p σ → WP isa (.block [.mov .r4 (Impl.AesGcm.Arm.imm 0)]) σ (DC p 0) := fun E =>
    Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t ht => by
      subst ht
      exact ⟨E.keep (fun r hr => by
          simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
        by simp [gpr_setReg]⟩
  refine rel_seq (rel_env E₁ E₂ [] (by simp) der0_check) (w0 E₁) (w0 E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  refine rel_loop (fun m t₁ t₂ => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ DC p i t₁ ∧ DC p i t₂)
    (fun m t₁ t₂ ⟨i, hm, hi, I₁, I₂⟩ => ?_) ((p.R / 2 - 1) - 0)
    ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, D₁, D₂⟩
  refine rel_seqQ (rel_env I₁.env I₂.env [.r4] (by simp [I₁.r4, I₂.r4]) derA_check) (derA_wp L I₁)
    (derA_wp L I₂) fun u₁ u₂ A₁ A₂ => ?_
  refine rel_seqQ (rel_ctr A₁.1 A₂.1 (A₁.2.env.sp_eq A₂.2.env)) (derC_wp A₁) (derC_wp A₂)
    fun a b J₁ J₂ => ?_
  refine rel_wpQ (rel_env J₁.env J₂.env [.r4] (by simp [J₁.r4, J₂.r4]) derP_check) (derP_wp L hi J₁)
    (derP_wp L hi J₂) fun a' b' ⟨K₁, z₁⟩ ⟨K₂, z₂⟩ => ?_
  have ev₁ := eval_ne' z₁
  have ev₂ := eval_ne' z₂
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : i + 1 ≠ p.R / 2 - 1 := by simpa using hc
  exact ⟨(p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, K₁, K₂⟩

theorem expA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block expandArgs) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem hkey_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block hkey) h).isSome
    = true := ⟨_, by taint_decide⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) keys TT := by
  refine rel_seq (derive_rel L E₁ E₂) (derive_ok L E₁) (derive_ok L E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  have wA : ∀ {τ : State}, Env p τ → WP isa (.block expandArgs) τ fun t₁ =>
      KeyCall t₁ (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 2048)
        (Spec.GcmSiv.keyLen p.R) ∧ Env p t₁ := fun E => by
    obtain ⟨t₁, run₁, kc, E', -⟩ := expArgs_ok L E
    exact WP.of_runBlock ⟨t₁, run₁, kc, E'⟩
  refine rel_seq (c₁ := expand) ?_ (WP.mono (expand_ok L D₁.env) fun _ X => X.env)
    (WP.mono (expand_ok L D₂.env) fun _ X => X.env) fun u₁ u₂ F₁ F₂ =>
      rel_env F₁ F₂ [] (by simp) hkey_check
  exact rel_seq (rel_env D₁.env D₂.env [] (by simp) expA_check) (wA D₁.env) (wA D₂.env)
    fun a b ⟨k₁, _⟩ ⟨k₂, _⟩ => rel_key k₁ k₂

end VG.Proof.AesGcmSiv.Arm
