import VerifiedGarbage.Proof.AesCcm.AArch64.Rel

/-!
# AES-CCM on AArch64: the tag and counter mode in two runs

Untrusted: everything here is checked by Lean. `tag y` and `ctr`, run from
two states that their correctness proofs describe with the same public
values, leak the same: the code between calls by the taint analysis
(`rel_env`), each call of `vg_aes_ctr32` by its proof
(`Proof.AesGcm.AArch64.rel_ctr`), and the chunks of `ctr` by induction on
the blocks left (`RelCT.loop`): both runs encrypt the same number of blocks
in each chunk, which depends only on the length.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite rel_ctr eval_zero eval_nonzero Others ctr_call CtrCall)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- Two runs from any states related by `P`, from those of each pair. -/
theorem rel_of_eq2 {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- What correctness says of the final states, added to two related runs. -/
theorem rel_post {σ₁ σ₂ : State} {c : Prog isa} {F₁ F₂ : State → Prop} (h : RelCT isa (Eq2 σ₁ σ₂) c TT)
    (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂) : RelCT isa (Eq2 σ₁ σ₂) c fun a b => F₁ a ∧ F₂ b :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

section
variable (v : Ctr32Impl) {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂)
include L E₁ E₂

/-- `tag y`. -/
theorem tag_rel {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    RelCT isa (Eq2 σ₁ σ₂) (tag v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (([imm .x9 0] : List Instr) ++ ctrAt ++ ctrArgs ++ ([ptr .x3 .x19 y, imm .x4 1] : List Instr))) h).isSome =
      true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seq (rel_env [] E₁ E₂ (by simp) t) (tagArgs_ok L E₁ hn₁ hc₁ hy) (tagArgs_ok L E₂ hn₂ hc₂ hy)
    fun τ₁ τ₂ ⟨F₁, C₁, _⟩ ⟨F₂, C₂, _⟩ => rel_ctr v C₁ C₂ (by rw [F₁.sp, F₂.sp])

/-- `ctrTail`. -/
theorem ctrTail_rel {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0)
    (h23₁ : σ₁.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h23₂ : σ₂.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16)) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16))
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 (c.n % 16)) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 (c.n % 16)) :
    RelCT isa (Eq2 σ₁ σ₂) (ctrTail v.callee) TT := by
  have hj : 1 + c.n / 16 < 256 ^ (15 - c.nl) := by
    have := L.hn
    have := Nat.le_self_pow (show 15 - c.nl ≠ 0 by have := L.h13; omega) 256
    omega
  -- After the call: the environment, the pointer and the length of the last bytes.
  have call : ∀ {σ τ : State}, σ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) →
      σ.gpr .x26 = BitVec.ofNat 64 (c.n % 16) → Env c τ →
      CtrCall τ c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80) (c.W + BitVec.ofNat 64 384) c.R 1 →
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] σ τ →
      WP isa (callCtr v.callee) τ fun ρ => Env c ρ ∧ ρ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧
        ρ.gpr .x26 = BitVec.ofNat 64 (c.n % 16) :=
    fun h23 h26 F C g => WP.mono (ctr_call v C) fun ρ h =>
      ⟨F.of_saved h.saved h.sp h.rd h.wr, by rw [h.saved _ (by decide) (by decide), g _ (by decide), h23],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h26]⟩
  refine rel_seq (rel_env [.x25] E₁ E₂ (by agree_tac [h25₁, h25₂]) ⟨_, by taint_decide⟩)
    (tailSetup_ok L hn₁ E₁ hc₁ hj h25₁) (tailSetup_ok L hn₂ E₂ hc₂ hj h25₂)
    fun τ₁ τ₂ ⟨F₁, C₁, _, _, _, g₁, _⟩ ⟨F₂, C₂, _, _, _, g₂, _⟩ => ?_
  refine rel_seq (rel_ctr v C₁ C₂ (by rw [F₁.sp, F₂.sp])) (call h23₁ h26₁ F₁ C₁ g₁) (call h23₂ h26₂ F₂ C₂ g₂)
    fun ρ₁ ρ₂ ⟨G₁, x23₁, x26₁⟩ ⟨G₂, x23₂, x26₂⟩ => ?_
  exact rel_env [.x23, .x26] G₁ G₂ (by agree_tac [x23₁, x23₂, x26₁, x26₂]) ⟨_, by taint_decide⟩

end

/-- One chunk, from two states after the same number of blocks. -/
theorem chunk_rel (v : Ctr32Impl) {c : Cx} (L : Lay c) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) {s₁ s₂ : State}
    (hc₁ : bytesAt s₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt s₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) {b : Nat} {σ₁ σ₂ : State}
    (I₁ : CtrInv c n₁ s₁ b σ₁) (I₂ : CtrInv c n₂ s₂ b σ₂) (hb : b < c.n / 16) :
    RelCT isa (Eq2 σ₁ σ₂) (ctrChunk v.callee) TT := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  refine RelCT.assoc (rel_seq (rel_env [.x24, .x25] I₁.env I₂.env (by agree_tac [I₁.x24, I₂.x24, I₁.x25, I₂.x25])
      ⟨_, by taint_decide⟩)
    (kSel_ok (b := b) I₁.x24 I₁.x25 (by omega)) (kSel_ok (b := b) I₂.x24 I₂.x25 (by omega))
    fun τ₁ τ₂ ⟨x26₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x26₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at x26₁ x26₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega
  have F₁ : Env c τ₁ := I₁.env.others g₁ (by decide) sp₁ rd₁ wr₁
  have F₂ : Env c τ₂ := I₂.env.others g₂ (by decide) sp₂ rd₂ wr₂
  have c0 : ∀ {n : List Byte} {s σ τ : State}, CtrInv c n s b σ → τ.mem = σ.mem →
      bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 →
      bytesAt τ.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 := fun I hm hc => by
    rw [hm, Proof.AesGcm.AArch64.bytesAt_frame I.frame (ctrR_disj L (.inl (by decide))) (by decide), hc]
  have y23₁ : τ₁.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) := by rw [g₁ _ (by decide), I₁.x23]
  have y23₂ : τ₂.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) := by rw [g₂ _ (by decide), I₂.x23]
  have y25₁ : τ₁.gpr .x25 = BitVec.ofNat 64 (1 + b) := by rw [g₁ _ (by decide), I₁.x25]
  have y25₂ : τ₂.gpr .x25 = BitVec.ofNat 64 (1 + b) := by rw [g₂ _ (by decide), I₂.x25]
  have y24₁ : τ₁.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) := by rw [g₁ _ (by decide), I₁.x24]
  have y24₂ : τ₂.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) := by rw [g₂ _ (by decide), I₂.x24]
  refine rel_seq (rel_env [.x23, .x25, .x26] F₁ F₂ (by agree_tac [y23₁, y23₂, y25₁, y25₂, x26₁, x26₂])
      ⟨_, by taint_decide⟩)
    (setup_ok L hn₁ hkb hk1 F₁ (c0 I₁ m₁ hc₁) y23₁ y25₁ x26₁) (setup_ok L hn₂ hkb hk1 F₂ (c0 I₂ m₂ hc₂) y23₂ y25₂ x26₂)
    fun ρ₁ ρ₂ ⟨G₁, C₁, _, _, h₁, _⟩ ⟨G₂, C₂, _, _, h₂, _⟩ => ?_
  have call : ∀ {τ ρ : State}, τ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) → τ.gpr .x25 = BitVec.ofNat 64 (1 + b) →
      τ.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) → τ.gpr .x26 = BitVec.ofNat 64 k → Env c ρ →
      CtrCall ρ c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384) c.R k →
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] τ ρ →
      WP isa (callCtr v.callee) ρ fun ω => Env c ω ∧ ω.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) ∧
        ω.gpr .x25 = BitVec.ofNat 64 (1 + b) ∧ ω.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) ∧
        ω.gpr .x26 = BitVec.ofNat 64 k :=
    fun h23 h25 h24 h26 G C g => WP.mono (ctr_call v C) fun ω h =>
      ⟨G.of_saved h.saved h.sp h.rd h.wr, by rw [h.saved _ (by decide) (by decide), g _ (by decide), h23],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h25],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h24],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h26]⟩
  refine rel_seq (rel_ctr v C₁ C₂ (by rw [G₁.sp, G₂.sp])) (call y23₁ y25₁ y24₁ x26₁ G₁ C₁ h₁)
    (call y23₂ y25₂ y24₂ x26₂ G₂ C₂ h₂) fun ω₁ ω₂ ⟨H₁, z23₁, z25₁, z24₁, z26₁⟩ ⟨H₂, z23₂, z25₂, z24₂, z26₂⟩ => ?_
  exact rel_env [.x23, .x24, .x25, .x26] H₁ H₂ (by agree_tac [z23₁, z23₂, z24₁, z24₂, z25₁, z25₂, z26₁, z26₂])
    ⟨_, by taint_decide⟩

/-- `ctr`. -/
theorem ctr_rel (v : Ctr32Impl) {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂)
    {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (ctr v.callee) TT := by
  have hn64 := L.n_lt
  refine RelCT.assoc (rel_seq ?_ (ctrHead_ok v L hn₁ E₁ hc₁) (ctrHead_ok v L hn₂ E₂ hc₂) fun τ₁ τ₂ I₁ I₂ => ?_)
  · refine rel_seq (rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩) (ctrHeadBlk_ok L (nonce := n₁) E₁)
      (ctrHeadBlk_ok L (nonce := n₂) E₂) fun τ₁ τ₂ I₁ I₂ => ?_
    have e₁ := eval_zero (a := c.n / 16) (by rw [I₁.x24, Nat.sub_zero]) (by omega)
    have e₂ := eval_zero (a := c.n / 16) (by rw [I₂.x24, Nat.sub_zero]) (by omega)
    refine rel_ite e₁ e₂ (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] I₁.env I₂.env (by simp) ⟨_, by taint_decide⟩
    have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine (RelCT.loop (Q := TT) (fun m a b => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧
        CtrInv c n₁ σ₁ j a ∧ CtrInv c n₂ σ₂ j b) (fun m => ?_) (c.n / 16 - 0)).mono
      (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨0, rfl, by omega, I₁, I₂⟩) fun _ _ h => h
    refine rel_of_eq2 fun a b ⟨j, hm, hj, J₁, J₂⟩ => ?_
    refine (rel_post (chunk_rel v L hn₁ hn₂ hc₁ hc₂ J₁ J₂ hj) (chunk_ok v L hn₁ hc₁ J₁ hj)
      (chunk_ok v L hn₂ hc₂ J₂ hj)).mono (fun _ _ h => h) fun a' b' ⟨⟨k, hk, hk1, hkb, K₁⟩, ⟨k', hk', _, _, K₂⟩⟩ => ?_
    have e : k = k' := by rw [hk, hk']
    subst e
    have ev₁ := eval_nonzero (r := .x24) (a := c.n / 16 - (j + k)) K₁.x24 (by omega)
    have ev₂ := eval_nonzero (r := .x24) (a := c.n / 16 - (j + k)) K₂.x24 (by omega)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + k), ?_, j + k, rfl, ?_, K₁, K₂⟩⟩
    · rw [ev₁] at ht; simp at ht; omega
    · rw [ev₁] at ht; simp at ht; omega
  · refine rel_seq (rel_env [] I₁.env I₂.env (by simp) ⟨_, by taint_decide⟩) (lastLen_ok L I₁.env) (lastLen_ok L I₂.env)
      fun ρ₁ ρ₂ ⟨x26₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x26₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
    have F₁ : Env c ρ₁ := I₁.env.others g₁ (by decide) sp₁ rd₁ wr₁
    have F₂ : Env c ρ₂ := I₂.env.others g₂ (by decide) sp₂ rd₂ wr₂
    refine rel_ite (eval_zero x26₁ (by omega)) (eval_zero x26₂ (by omega)) (fun _ => ?_) (fun _ => ?_)
    · exact rel_env [] F₁ F₂ (by simp) ⟨_, by taint_decide⟩
    · have c0 : ∀ {n : List Byte} {s σ τ : State}, CtrInv c n s (c.n / 16) σ → τ.mem = σ.mem →
          bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 →
          bytesAt τ.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 := fun I hm hc => by
        rw [hm, Proof.AesGcm.AArch64.bytesAt_frame I.frame (ctrR_disj L (.inl (by decide))) (by decide), hc]
      exact ctrTail_rel v L F₁ F₂ hn₁ hn₂ (c0 I₁ m₁ hc₁) (c0 I₂ m₂ hc₂)
        (by rw [g₁ _ (by decide), I₁.x23]) (by rw [g₂ _ (by decide), I₂.x23])
        (by rw [g₁ _ (by decide), I₁.x25]) (by rw [g₂ _ (by decide), I₂.x25]) x26₁ x26₂

end VG.Proof.AesCcm.AArch64
