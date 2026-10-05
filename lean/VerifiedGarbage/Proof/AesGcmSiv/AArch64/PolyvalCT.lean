import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-GCM-SIV on AArch64: relating two runs, the keys and POLYVAL

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2`) piece by piece, as AES-GCM's do
(`Proof.AesGcm.AArch64.rel_seq`): the code between calls by the taint
analysis, from the registers that hold the public arguments in both runs
(`Env`, `rel_env`) and those the pieces pin to the same values; each call
by its callee's proof; and the next piece from the states the correctness
proofs describe.
-/

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_taint)

theorem Env.agree {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) :
    ∀ r ∈ envRegs, τ₁.gpr r = τ₂.gpr r := by
  intro r hr
  simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [E₁.x19, E₂.x19]
  · rw [E₁.x20, E₂.x20]
  · rw [E₁.x21, E₂.x21]
  · rw [E₁.x22, E₂.x22]
  · rw [E₁.x23, E₂.x23]
  · rw [E₁.x24, E₂.x24]
  · rw [E₁.x25, E₂.x25]
  · rw [E₁.x26, E₂.x26]

theorem Env.sp_eq {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) : τ₁.sp = τ₂.sp := by
  rw [E₁.sp, E₂.sp]

/-- The registers holding the public arguments, and `rs`. -/
abbrev pubRegs (rs : List Reg) : List Reg := envRegs ++ rs

/-- Code the taint analysis checks, from the registers holding the public
arguments and the registers `rs` the two runs agree on. -/
theorem rel_env {c : Prog isa} {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ rs)) c h).isSome = true) :
    RelCT isa (Eq2 τ₁ τ₂) c TT :=
  rel_taint (envRegs ++ rs) (E₁.sp_eq E₂) (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) hc

/-- Then, towards any relation of the final states. -/
theorem rel_seqQ {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- The last piece, with what correctness says of each run's final state. -/
theorem rel_wpQ {c : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h : RelCT isa (Eq2 σ₁ σ₂) c TT) (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂)
    (hq : ∀ a b, F₁ a → F₂ b → Q a b) : RelCT isa (Eq2 σ₁ σ₂) c Q :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun a b h => hq a b h.2.1 h.2.2

/-- `a; (b; (c; (d; e)))`, related as `(a; (b; (c; d))); e`. -/
theorem RelCT.assoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
  | seq d₁ e₁' =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
  | seq d₂ e₂' =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) e₁')
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) e₂')
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- A loop step in two runs: the condition agrees, and the runs are related
anew while it loops. -/
theorem rel_loop {body : Prog isa} {c : Cond} (I : Nat → State → State → Prop)
    (hstep : ∀ n σ₁ σ₂, I n σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) body fun s₁ s₂ => isa.eval c s₁ = isa.eval c s₂ ∧
      (isa.eval c s₁ = some true → ∃ m < n, I m s₁ s₂))
    (n : Nat) {σ₁ σ₂ : State} (h : I n σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.loop body c) TT := by
  refine (RelCT.loop (Q := TT) I (fun n => ?_) n).mono (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact h)
    fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hc, hi⟩ := hstep n s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, hc, fun _ => trivial, hi⟩

end VG.Proof.AesGcmSiv.AArch64

/-!
## The keys are constant time

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

/-!
## POLYVAL is constant time

Untrusted: everything here is checked by Lean. Both runs absorb the same
chunks of blocks: their number depends only on the lengths, which are
public; the code around each call of `vg_ghash` passes the taint analysis,
and each call has the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_gh rel_ite GcmImpl GhCall gh_call eval_zero eval_nonzero Others)

theorem chunkPre_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28])) chunkPre h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkEnd_check :
    ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x28])) (.block [.lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A chunk, in two runs with the same public arguments, pointer and count. -/
theorem chunk_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ₁ : Src p τ₁ Q (16 * (m / 16)))
    (hQ₂ : Src p τ₂ Q (16 * (m / 16))) (a27 : τ₁.gpr .x27 = Q) (b27 : τ₂.gpr .x27 = Q)
    (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 m) (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 τ₁ τ₂) (chunk v.callees) TT := by
  refine rel_seq (rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) chunkPre_check)
    (chunkPre_ok L E₁ hm h16 hQ₁ a27 a28) (chunkPre_ok L E₂ hm h16 hQ₂ b27 b28) fun u₁ u₂ P₁ P₂ => ?_
  have wG : ∀ {u : State}, ChunkPre p Q m (min (m / 16) 64) τ₁ u ∨ ChunkPre p Q m (min (m / 16) 64) τ₂ u →
      WP isa (callGh v.callees) u fun w => Env p w ∧ w.gpr .x28 = BitVec.ofNat 64 (m - 16 * min (m / 16) 64) :=
    fun h => by
      rcases h with P | P <;>
      exact WP.mono (gh_call v.gh P.call) fun _ G =>
        ⟨P.env.of_saved G.saved G.sp G.rd G.wr, by rw [G.saved _ (by decide) (by decide), P.x28]⟩
  exact rel_seq (rel_gh v.gh P₁.call P₂.call (P₁.env.sp_eq P₂.env)) (wG (.inl P₁)) (wG (.inr P₂))
    fun w₁ w₂ G₁ G₂ => rel_env G₁.1 G₂.1 [.x28] (by simp [G₁.2, G₂.2]) chunkEnd_check

/-- The chunks, in two runs from `σ₁` and `σ₂` with the same public arguments. -/
theorem chunks_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (h16 : 16 ≤ m) (hQ₁ : Src p σ₁ Q (16 * (m / 16))) (hQ₂ : Src p σ₂ Q (16 * (m / 16))) {d : Nat}
    (hd : d < m / 16) {τ₁ τ₂ : State} (I₁ : CInv p σ₁ Q m d τ₁) (I₂ : CInv p σ₂ Q m d τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop (chunk v.callees) (.nonzero .x .x9)) TT := by
  refine rel_loop (fun k t₁ t₂ => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p σ₁ Q m d t₁ ∧ CInv p σ₂ Q m d t₂)
    (fun k t₁ t₂ ⟨d, hk, hd, J₁, J₂⟩ => ?_) (m / 16 - d) ⟨d, rfl, hd, I₁, I₂⟩
  refine rel_wpQ (chunk_rel v L J₁.abs.env J₂.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) (J₂.src hQ₂ hd)
      J₁.x27 J₂.x27 J₁.x28 J₂.x28)
    (chunk_ok v L J₁.abs.env (by omega) (by omega) (J₁.src hQ₁ hd) J₁.x27 J₁.x28)
    (chunk_ok v L J₂.abs.env (by omega) (by omega) (J₂.src hQ₂ hd) J₂.x27 J₂.x28) fun a b C₁ C₂ => ?_
  obtain ⟨K₁, x9₁⟩ := J₁.step L hm hQ₁ hd C₁
  obtain ⟨K₂, x9₂⟩ := J₂.step L hm hQ₂ hd C₂
  have ev₁ := eval_nonzero x9₁ (by omega)
  have ev₂ := eval_nonzero x9₂ (by omega)
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : d + min (m / 16 - d) 64 ≠ m / 16 := by simp at hc; omega
  exact ⟨m / 16 - (d + min (m / 16 - d) 64), by omega, d + min (m / 16 - d) 64, rfl, by omega, K₁, K₂⟩

theorem absHead_check :
    ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28])) (.block [.lsr .x .x9 .x28 4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem absTailPre_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [.x27, .x28])) absTailPre h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `chunk` on the block at `W + 224`. -/
theorem chunkB_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (a27 : τ₁.gpr .x27 = p.W + BitVec.ofNat 64 224) (b27 : τ₂.gpr .x27 = p.W + BitVec.ofNat 64 224)
    (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 16) (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 16) :
    RelCT isa (Eq2 τ₁ τ₂) (chunk v.callees) TT :=
  chunk_rel v L E₁ E₂ (m := 16) (by decide) (by decide) (srcB L E₁.perm) (srcB L E₂.perm) a27 b27 a28 b28

/-- `absorb`, in two runs with the same public arguments, pointer and count. -/
theorem absorb_rel (v : GcmImpl) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (hw : Q.toNat + m ≤ 2 ^ 64) (hd : (⟨Q, m⟩ : Region).Disjoint ⟨p.W, 3808⟩)
    (hc₁ : Covers [⟨Q, m⟩] (τ₁.rd ++ τ₁.wr)) (hc₂ : Covers [⟨Q, m⟩] (τ₂.rd ++ τ₂.wr))
    (a27 : τ₁.gpr .x27 = Q) (b27 : τ₂.gpr .x27 = Q) (a28 : τ₁.gpr .x28 = BitVec.ofNat 64 m)
    (b28 : τ₂.gpr .x28 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 τ₁ τ₂) (absorb v.callees) TT := by
  have hQ₁ : Src p τ₁ Q m := Src.ofW L hc₁ hm hw hd
  have hQ₂ : Src p τ₂ Q m := Src.ofW L hc₂ hm hw hd
  refine rel_seq (rel_env E₁ E₂ [.x27, .x28] (by simp [a27, b27, a28, b28]) absHead_check) (absHead_ok hm a28)
    (absHead_ok hm b28) fun u₁ u₂ ⟨x9₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x9₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : Env p u₁ := E₁.keep (fun q hq => ho₁ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have F₂ : Env p u₂ := E₂.keep (fun q hq => ho₂ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  have u27₁ : u₁.gpr .x27 = Q := by rw [ho₁ _ (by decide), a27]
  have u27₂ : u₂.gpr .x27 = Q := by rw [ho₂ _ (by decide), b27]
  have u28₁ : u₁.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₁ _ (by decide), a28]
  have u28₂ : u₂.gpr .x28 = BitVec.ofNat 64 m := by rw [ho₂ _ (by decide), b28]
  have hQ₁' := hQ₁.of_eq rd₁ wr₁
  have hQ₂' := hQ₂.of_eq rd₂ wr₂
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_zero x9₁ (by omega)) (eval_zero x9₂ (by omega))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_))
    (absMid_ok v L F₁ hm hQ₁' u27₁ u28₁ x9₁) (absMid_ok v L F₂ hm hQ₂' u27₂ u28₂ x9₂)
    fun w₁ w₂ ⟨A₁, x27₁, x28₁⟩ ⟨A₂, x27₂, x28₂⟩ => ?_
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_rel v L hm (by omega) (hQ₁'.take (by omega)) (hQ₂'.take (by omega)) (d := 0) (by omega)
      (CInv.zero F₁ u27₁ u28₁) (CInv.zero F₂ u27₂ u28₂)
  -- The last bytes.
  refine rel_ite (eval_zero x28₁ (by omega)) (eval_zero x28₂ (by omega))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_)
  have h0 : m % 16 ≠ 0 := by simpa using hf
  have dT : (⟨Q + BitVec.ofNat 64 (16 * (m / 16)), m % 16⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    hd.sub_left (Offset.sub_base Q (by omega))
  have hs₁ := (hQ₁'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega)).of_eq A₁.rd A₁.wr
  have hs₂ := (hQ₂'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega)).of_eq A₂.rd A₂.wr
  refine rel_seq (rel_env A₁.env A₂.env [.x27, .x28] (by simp [x27₁, x27₂, x28₁, x28₂]) absTailPre_check)
    (absTailPre_ok L A₁.env (by omega) (by omega) hs₁.rd dT x27₁ x28₁)
    (absTailPre_ok L A₂.env (by omega) (by omega) hs₂.rd dT x27₂ x28₂) fun z₁ z₂ T₁ T₂ => ?_
  exact chunkB_rel v L T₁.env T₂.env T₁.x27 T₂.x27 T₁.x28 T₂.x28

theorem lensBlock_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block lensBlock) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagIn_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs [])) (.block tagIn) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyA_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.block [Impl.AesGcm.AArch64.mov .x27 .x23, Impl.AesGcm.AArch64.mov .x28 .x24]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyD_check : ∃ h, (taint.check (Taint.ofRegs (pubRegs []))
    (.block [Impl.AesGcm.AArch64.mov .x27 .x25, Impl.AesGcm.AArch64.mov .x28 .x26]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Two registers set to the arguments in `x19`–`x26`. -/
theorem mov2_ok {p : Prm} {t : State} (E : Env p t) {a b : Reg} (_ha : a ∈ envRegs) (hb : b ∈ envRegs) :
    WP isa (.block [Impl.AesGcm.AArch64.mov .x27 a, Impl.AesGcm.AArch64.mov .x28 b]) t fun t' =>
      Env p t' ∧ t'.gpr .x27 = t.gpr a ∧ t'.gpr .x28 = t.gpr b ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine WP.of_runBlock ⟨_, by grun [], ?_⟩
  have hb' : b ≠ .x27 := fun e => by subst e; revert hb; decide
  exact ⟨(E.write (by decide) _).write (by decide) _, by simp [gpr_write], by simp [gpr_write, hb'], rfl, rfl, rfl⟩

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (polyval v.callees) TT := by
  refine rel_seq (rel_env E₁ E₂ [] (by simp) polyA_check) (mov2_ok E₁ (a := .x23) (b := .x24) (by decide) (by decide))
    (mov2_ok E₂ (a := .x23) (b := .x24) (by decide) (by decide)) fun a₁ a₂ ⟨G₁, a27₁, a28₁, _, rd₁, wr₁⟩
      ⟨G₂, a27₂, a28₂, _, rd₂, wr₂⟩ => ?_
  rw [E₁.x23] at a27₁; rw [E₁.x24] at a28₁; rw [E₂.x23] at a27₂; rw [E₂.x24] at a28₂
  have hc₁ : Covers [⟨p.A, p.al⟩] (a₁.rd ++ a₁.wr) := G₁.perm.aad
  have hc₂ : Covers [⟨p.A, p.al⟩] (a₂.rd ++ a₂.wr) := G₂.perm.aad
  refine rel_seq (absorb_rel v L G₁ G₂ L.al_lt L.aw L.a_w hc₁ hc₂ a27₁ a27₂ a28₁ a28₂)
    (absorb_ok v L G₁ hc₁ L.al_lt L.aw L.a_w a27₁ a28₁) (absorb_ok v L G₂ hc₂ L.al_lt L.aw L.a_w a27₂ a28₂)
    fun b₁ b₂ B₁ B₂ => ?_
  refine rel_seq (rel_env B₁.env B₂.env [] (by simp) polyD_check)
    (mov2_ok B₁.env (a := .x25) (b := .x26) (by decide) (by decide))
    (mov2_ok B₂.env (a := .x25) (b := .x26) (by decide) (by decide)) fun c₁ c₂ ⟨H₁, c27₁, c28₁, _, _, _⟩
      ⟨H₂, c27₂, c28₂, _, _, _⟩ => ?_
  rw [B₁.env.x25] at c27₁; rw [B₁.env.x26] at c28₁; rw [B₂.env.x25] at c27₂; rw [B₂.env.x26] at c28₂
  have dc₁ : Covers [⟨p.D, p.n⟩] (c₁.rd ++ c₁.wr) := Proof.AesGcm.AArch64.covers_left H₁.perm.d
  have dc₂ : Covers [⟨p.D, p.n⟩] (c₂.rd ++ c₂.wr) := Proof.AesGcm.AArch64.covers_left H₂.perm.d
  refine rel_seq (absorb_rel v L H₁ H₂ L.n_lt L.dw L.d_w dc₁ dc₂ c27₁ c27₂ c28₁ c28₂)
    (absorb_ok v L H₁ dc₁ L.n_lt L.dw L.d_w c27₁ c28₁) (absorb_ok v L H₂ dc₂ L.n_lt L.dw L.d_w c27₂ c28₂)
    fun d₁ d₂ D₁ D₂ => ?_
  refine rel_seq (c₁ := lens v.callees) ?_ (lens_ok v L D₁.env) (lens_ok v L D₂.env) fun e₁ e₂ F₁ F₂ =>
    rel_env F₁.env F₂.env [] (by simp) tagIn_check
  have wL : ∀ {d : State}, Env p d → WP isa (.block lensBlock) d fun t =>
      Env p t ∧ t.gpr .x27 = p.W + BitVec.ofNat 64 224 ∧ t.gpr .x28 = BitVec.ofNat 64 16 := fun E => by
    have w₀ := E.perm.wW (show 224 + 8 ≤ 3808 by decide)
    have w₈ := E.perm.wW (show 232 + 8 ≤ 3808 by decide)
    refine WP.run ⟨_, by simp only [lensBlock]; grun [E.x19, E.x24, E.x26, w₀, w₈], rfl⟩ fun t ht => ?_
    subst ht
    refine ⟨E.keep (fun q hq => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
      by simp [gpr_write, E.x19], by simp [gpr_write, movz_lit (show 16 < 2 ^ 16 by decide)]⟩
  exact rel_seq (rel_env D₁.env D₂.env [] (by simp) lensBlock_check) (wL D₁.env) (wL D₂.env)
    fun f₁ f₂ ⟨K₁, x27₁, x28₁⟩ ⟨K₂, x27₂, x28₂⟩ => chunkB_rel v L K₁ K₂ x27₁ x27₂ x28₁ x28₂

end VG.Proof.AesGcmSiv.AArch64
