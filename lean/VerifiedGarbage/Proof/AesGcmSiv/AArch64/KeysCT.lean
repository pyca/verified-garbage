import VerifiedGarbage.Proof.AesGcmSiv.AArch64.CTBase

/-!
# AES-GCM-SIV on AArch64: the keys are constant time

Untrusted: everything here is checked by Lean. Both runs derive the same
number of blocks (`rounds / 2 − 1`, from `x22`); the code around the calls
passes the taint analysis, and each call has the same arguments in both
runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ctr rel_key GcmImpl CtrCall ctr_call KeyCall key_call eval_nonzero
  Others)

/-- A run of `derive` before block `i`. -/
structure DC (p : Prm) (i : Nat) (t : State) : Prop where
  env : Env p t
  x27 : t.gpr .x27 = BitVec.ofNat 64 i

theorem derA_wp {p : Prm} (L : Lay p) {i : Nat} {t : State} (h : DC p i t) :
    WP isa (.block deriveBlock) t fun t₁ =>
      CtrCall t₁ p.K (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 224) (p.W + BitVec.ofNat 64 1760) p.R 1 ∧
        DC p i t₁ := by
  obtain ⟨t₁, run₁, -, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := derArgs_ok h.env h.x27
  have E₁ : Env p t₁ := h.env.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  exact WP.of_runBlock ⟨t₁, run₁, derCall L E₁ x0 x1 x2 x3 x4 x5, E₁, by rw [ho₁ _ (by decide), h.x27]⟩

theorem derC_wp (v : GcmImpl) {p : Prm} {i : Nat} {t : State}
    (h : CtrCall t p.K (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 224) (p.W + BitVec.ofNat 64 1760) p.R 1 ∧
      DC p i t) :
    WP isa (callCtr v.callees) t (DC p i) :=
  WP.mono (ctr_call v.ctr h.1) fun _ P =>
    ⟨h.2.env.of_saved P.saved P.sp P.rd P.wr, by rw [P.saved _ (by decide) (by decide), h.2.x27]⟩

theorem derP_wp {p : Prm} (L : Lay p) {i : Nat} (hi : i < p.R / 2 - 1) {t : State} (h : DC p i t) :
    WP isa (.block derivePost) t fun t' =>
      DC p (i + 1) t' ∧ t'.gpr .x10 = BitVec.ofNat 64 (p.R / 2 - 1 - (i + 1)) := by
  obtain ⟨t', run', -, x27', x10', ho', sp', rd', wr'⟩ := derPost_ok L h.env hi h.x27
  exact WP.of_runBlock ⟨t', run', ⟨h.env.keep (fun r hr => ho' r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp' rd' wr', x27'⟩, x10'⟩

theorem derA_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27])) (.block deriveBlock) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem derP_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27])) (.block derivePost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem der0_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block [Impl.AesGcm.AArch64.imm .x27 0]) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- `derive`, in two runs with the same public arguments. -/
theorem derive_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (derive v.callees) TT := by
  have hR := L.rounds
  have w0 : ∀ {σ : State}, Env p σ → WP isa (.block [Impl.AesGcm.AArch64.imm .x27 0]) σ (DC p 0) := fun E =>
    WP.run ⟨_, by grun [], rfl⟩ fun t ht => by
      subst ht
      exact ⟨E.keep (fun r hr => by
          simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
        by simp [gpr_write]⟩
  refine rel_seq (rel_env E₁ E₂ [] (by simp) der0_check) (w0 E₁) (w0 E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  refine rel_loop (fun m t₁ t₂ => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ DC p i t₁ ∧ DC p i t₂)
    (fun m t₁ t₂ ⟨i, hm, hi, I₁, I₂⟩ => ?_) ((p.R / 2 - 1) - 0) ⟨0, rfl, by omega, D₁, D₂⟩
  refine rel_seqQ (rel_env I₁.env I₂.env [.x27] (by simp [I₁.x27, I₂.x27]) derA_check) (derA_wp L I₁)
    (derA_wp L I₂) fun u₁ u₂ A₁ A₂ => ?_
  refine rel_seqQ (rel_ctr v.ctr A₁.1 A₂.1 (A₁.2.env.sp_eq A₂.2.env)) (derC_wp v A₁) (derC_wp v A₂)
    fun a b J₁ J₂ => ?_
  refine rel_wpQ (rel_env J₁.env J₂.env [.x27] (by simp [J₁.x27, J₂.x27]) derP_check) (derP_wp L hi J₁)
    (derP_wp L hi J₂) fun a' b' ⟨K₁, x10₁⟩ ⟨K₂, x10₂⟩ => ?_
  have ev₁ := eval_nonzero x10₁ (by omega)
  have ev₂ := eval_nonzero x10₂ (by omega)
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : i + 1 ≠ p.R / 2 - 1 := by simp at hc; omega
  exact ⟨(p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, K₁, K₂⟩

theorem expA_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block expandArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem hkey_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block hkey) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (keys v.callees) TT := by
  refine rel_seq (derive_rel v L E₁ E₂) (derive_ok v L E₁) (derive_ok v L E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  have wA : ∀ {τ : State}, Env p τ → WP isa (.block expandArgs) τ fun t₁ =>
      KeyCall t₁ (p.W + BitVec.ofNat 64 32) (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 1760)
        (Spec.GcmSiv.keyLen p.R) ∧ Env p t₁ := fun E => by
    obtain ⟨t₁, run₁, kc, E', -⟩ := expArgs_ok L E
    exact WP.of_runBlock ⟨t₁, run₁, kc, E'⟩
  refine rel_seq (c₁ := expand v.callees) ?_ (WP.mono (expand_ok v L D₁.env) fun _ X => X.env)
    (WP.mono (expand_ok v L D₂.env) fun _ X => X.env) fun u₁ u₂ F₁ F₂ =>
      rel_env F₁ F₂ [] (by simp) hkey_check
  refine rel_seq (rel_env D₁.env D₂.env [] (by simp) expA_check) (wA D₁.env) (wA D₂.env)
    fun a b ⟨k₁, A₁⟩ ⟨k₂, A₂⟩ => rel_key v.key k₁ k₂ (A₁.sp_eq A₂)

end VG.Proof.AesGcmSiv.AArch64
