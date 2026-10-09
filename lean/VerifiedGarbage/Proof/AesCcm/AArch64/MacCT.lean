import VerifiedGarbage.Proof.AesCcm.AArch64.Rel

/-!
# AES-CCM on AArch64: the CBC-MAC in two runs

Untrusted: everything here is checked by Lean. Each piece of `mac y`, run
from two states that its correctness proof describes with the same public
values, leaks the same: the code between calls by the taint analysis
(`rel_env`), from the environment's registers and those the correctness
proofs pin (the pointer and the length in `x23` and `x24`), and each call of
`vg_cmac_aes_update` by its proof (`rel_upd`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop minK)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite eval_zero Others)
open VG.Proof.CmacAes.Stream.AArch64 (upd_call)
open VG.Proof.AesCcm (headLen)

section
variable (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁)
  (E₂ : Env c σ₂) {y : Nat} (hy : y = 0 ∨ y = 96)
include L E₁ E₂ hy

/-- `updBlock y`. -/
theorem updBlock_rel : RelCT isa (Eq2 σ₁ σ₂) (updBlock v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (updArgs y ++ ([ptr .x3 .x19 bO, imm .x4 1] : List Instr))) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seq (rel_env [] E₁ E₂ (by simp) t) (updArgs_ok L E₁ hy) (updArgs_ok L E₂ hy)
    fun τ₁ τ₂ ⟨F₁, A₁, _⟩ ⟨F₂, A₂, _⟩ => rel_upd v A₁ A₂ (by rw [F₁.sp, F₂.sp])

/-- `absTail y`. -/
theorem absTail_rel {P : Addr} {len : Nat} (hP₁ : Buf c σ₁ P len) (hP₂ : Buf c σ₂ P len)
    (h23₁ : σ₁.gpr .x23 = P) (h23₂ : σ₂.gpr .x23 = P) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 len)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 len) (h13₁ : σ₁.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h13₂ : σ₂.gpr .x13 = BitVec.ofNat 64 (len % 16)) (h0 : len % 16 ≠ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (absTail v.callee y) TT := by
  refine RelCT.assoc (rel_seq (rel_env [.x23, .x24, .x13] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂, h13₁, h13₂])
      ⟨_, by taint_decide⟩)
    (absTailPre_ok E₁ hP₁ h23₁ h24₁ h13₁ h0) (absTailPre_ok E₂ hP₂ h23₂ h24₂ h13₂ h0) fun τ₁ τ₂ a₁ a₂ => ?_)
  exact updBlock_rel v L a₁.1 a₂.1 hy

/-- `absorbPad y`. -/
theorem absorbPad_rel {P : Addr} {len : Nat} (hP₁ : Buf c σ₁ P len) (hP₂ : Buf c σ₂ P len)
    (h23₁ : σ₁.gpr .x23 = P) (h23₂ : σ₂.gpr .x23 = P) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 len)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 len) :
    RelCT isa (Eq2 σ₁ σ₂) (absorbPad v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.x23, .x24]))
      (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have hl := hP₁.lt
  -- After the call: the environment, the string's pointer and length.
  have call : ∀ {σ τ : State}, Env c σ → Buf c σ P len → σ.gpr .x23 = P → σ.gpr .x24 = BitVec.ofNat 64 len →
      Proof.CmacAes.Stream.AArch64.UArgs τ c.K (c.W + BitVec.ofNat 64 y) P (c.W + BitVec.ofNat 64 384) c.R
        (len / 16) → Env c τ → Others [.x0, .x1, .x2, .x3, .x4, .x5] σ τ → τ.rd = σ.rd → τ.wr = σ.wr →
      WP isa (callUpdate v.callee) τ fun ρ => Env c ρ ∧ Buf c ρ P len ∧ ρ.gpr .x23 = P ∧
        ρ.gpr .x24 = BitVec.ofNat 64 len :=
    fun _ hP h23 h24 U F g rd wr => WP.mono (upd_call v v.callee.name U) fun ρ h =>
      ⟨F.of_saved h.saved h.sp h.rd h.wr, hP.of_eq (by rw [h.rd, rd]) (by rw [h.wr, wr]),
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h23],
        by rw [h.saved _ (by decide) (by decide), g _ (by decide), h24]⟩
  refine rel_seq (rel_env [.x23, .x24] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂]) t)
    (absArgs_ok L E₁ hy hP₁ h23₁ h24₁) (absArgs_ok L E₂ hy hP₂ h23₂ h24₂)
    fun τ₁ τ₂ ⟨U₁, F₁, g₁, _, rd₁, wr₁⟩ ⟨U₂, F₂, g₂, _, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_upd v U₁ U₂ (by rw [F₁.sp, F₂.sp])) (call E₁ hP₁ h23₁ h24₁ U₁ F₁ g₁ rd₁ wr₁)
    (call E₂ hP₂ h23₂ h24₂ U₂ F₂ g₂ rd₂ wr₂) fun ρ₁ ρ₂ ⟨G₁, B₁, x23₁, x24₁⟩ ⟨G₂, B₂, x23₂, x24₂⟩ => ?_
  refine rel_seq (rel_env [.x24] G₁ G₂ (by agree_tac [x24₁, x24₂]) ⟨_, by taint_decide⟩)
    (absMask_ok hl x24₁) (absMask_ok hl x24₂)
    fun κ₁ κ₂ ⟨x13₁, og₁, _, sp₁, rd₁', wr₁'⟩ ⟨x13₂, og₂, _, sp₂, rd₂', wr₂'⟩ => ?_
  have H₁ : Env c κ₁ := G₁.others og₁ (by decide) sp₁ rd₁' wr₁'
  have H₂ : Env c κ₂ := G₂.others og₂ (by decide) sp₂ rd₂' wr₂'
  refine rel_ite (eval_zero x13₁ (by omega_arith)) (eval_zero x13₂ (by omega_arith)) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] H₁ H₂ (by simp) ⟨_, by taint_decide⟩
  · exact absTail_rel v L H₁ H₂ hy (B₁.of_eq rd₁' wr₁') (B₂.of_eq rd₂' wr₂')
      (by rw [og₁ _ (by decide), x23₁]) (by rw [og₂ _ (by decide), x23₂])
      (by rw [og₁ _ (by decide), x24₁]) (by rw [og₂ _ (by decide), x24₂]) x13₁ x13₂ (of_decide_eq_false hf)

/-- `aadHead y`. -/
theorem aadHead_rel {A : Addr} {a : Nat} (hA₁ : Buf c σ₁ A a) (hA₂ : Buf c σ₂ A a) (ha0 : 0 < a)
    (h23₁ : σ₁.gpr .x23 = A) (h23₂ : σ₂.gpr .x23 = A) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 a)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 a) :
    RelCT isa (Eq2 σ₁ σ₂) (aadHead v.callee y) TT :=
  rel_assoc5 (rel_seq (rel_env [.x23, .x24] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (aadHeadPre_ok E₁ hA₁ ha0 h23₁ h24₁) (aadHeadPre_ok E₂ hA₂ ha0 h23₂ h24₂)
    fun _ _ a₁ a₂ => updBlock_rel v L a₁.1 a₂.1 hy)

/-- The associated data, if there is any. -/
theorem aadPart_rel (h23₁ : σ₁.gpr .x23 = c.A) (h23₂ : σ₂.gpr .x23 = c.A)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 c.al) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 c.al) :
    RelCT isa (Eq2 σ₁ σ₂) (.ite (.zero .x .x24) (.block []) (.seq (aadHead v.callee y) (absorbPad v.callee y)))
      TT := by
  have ha := L.al_lt
  refine rel_ite (eval_zero h24₁ ha) (eval_zero h24₂ ha) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩
  have h0 : c.al ≠ 0 := of_decide_eq_false hf
  have hA₁ := L.bufA E₁.perm
  have hA₂ := L.bufA E₂.perm
  refine rel_seq (aadHead_rel v L E₁ E₂ hy hA₁ hA₂ (by omega_arith) h23₁ h23₂ h24₁ h24₂)
    (aadHead_ok v L E₁ hy hA₁ (by omega_arith) h23₁ h24₁) (aadHead_ok v L E₂ hy hA₂ (by omega_arith) h23₂ h24₂)
    fun τ₁ τ₂ A₁ A₂ => ?_
  have hn1 : headLen c.al ≤ c.al := by unfold headLen; omega_arith
  exact absorbPad_rel v L A₁.env A₂.env hy ((hA₁.drop hn1).of_eq A₁.rd A₁.wr) ((hA₂.drop hn1).of_eq A₂.rd A₂.wr)
    A₁.x23 A₂.x23 A₁.x24 A₂.x24

/-- `b0 y`. -/
theorem b0_rel (S₁ : Slots c σ₁.mem) (S₂ : Slots c σ₂.mem) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 c.al)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 c.al) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (b0 v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [])) (.block (b0Seg y)) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (rel_env [.x24] E₁ E₂ (by agree_tac [h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (flags_ok L E₁ S₁ h24₁) (flags_ok L E₂ S₂ h24₂)
    fun τ₁ τ₂ ⟨x9₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x9₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : Env c τ₁ := E₁.others g₁ (by decide) sp₁ rd₁ wr₁
  have F₂ : Env c τ₂ := E₂.others g₂ (by decide) sp₂ rd₂ wr₂
  exact rel_seq (rel_env [] F₁ F₂ (by simp) t) (b0Seg_ok L F₁ hn₁ (by rw [m₁]; exact hc₁) x9₁ hy)
    (b0Seg_ok L F₂ hn₂ (by rw [m₂]; exact hc₂) x9₂ hy) fun _ _ a₁ a₂ => updBlock_rel v L a₁.1 a₂.1 hy

/-- `mac y`. -/
theorem mac_rel (S₁ : Slots c σ₁.mem) (S₂ : Slots c σ₂.mem) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (mac v.callee y) TT := by
  refine rel_seq (rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩) (aadLd_ok E₁ S₁) (aadLd_ok E₂ S₂)
    fun τ₁ τ₂ ⟨x23₁, x24₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x23₂, x24₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : Env c τ₁ := E₁.others g₁ (by decide) sp₁ rd₁ wr₁
  have F₂ : Env c τ₂ := E₂.others g₂ (by decide) sp₂ rd₂ wr₂
  refine rel_seq (b0_rel v L F₁ F₂ hy (by rw [m₁]; exact S₁) (by rw [m₂]; exact S₂) x24₁ x24₂ hn₁ hn₂
      (by rw [m₁]; exact hc₁) (by rw [m₂]; exact hc₂))
    (b0_ok v L F₁ (by rw [m₁]; exact S₁) x24₁ hn₁ (by rw [m₁]; exact hc₁) hy)
    (b0_ok v L F₂ (by rw [m₂]; exact S₂) x24₂ hn₂ (by rw [m₂]; exact hc₂) hy)
    fun κ₁ κ₂ ⟨M₁, y23₁, y24₁⟩ ⟨M₂, y23₂, y24₂⟩ => ?_
  refine rel_seq (aadPart_rel v L M₁.env M₂.env hy (by rw [y23₁, x23₁]) (by rw [y23₂, x23₂])
      (by rw [y24₁, x24₁]) (by rw [y24₂, x24₂]))
    (aadPart_ok v L M₁.env hy (by rw [y23₁, x23₁]) (by rw [y24₁, x24₁]))
    (aadPart_ok v L M₂.env hy (by rw [y23₂, x23₂]) (by rw [y24₂, x24₂])) fun ρ₁ ρ₂ P₁ P₂ => ?_
  refine rel_seq (rel_env [] P₁.env P₂.env (by simp) ⟨_, by taint_decide⟩) (dataArgs_ok P₁.env) (dataArgs_ok P₂.env)
    fun ω₁ ω₂ ⟨z23₁, z24₁, h₁, _, sp₁', rd₁', wr₁'⟩ ⟨z23₂, z24₂, h₂, _, sp₂', rd₂', wr₂'⟩ => ?_
  have G₁ : Env c ω₁ := P₁.env.others h₁ (by decide) sp₁' rd₁' wr₁'
  have G₂ : Env c ω₂ := P₂.env.others h₂ (by decide) sp₂' rd₂' wr₂'
  exact absorbPad_rel v L G₁ G₂ hy (L.bufD G₁.perm) (L.bufD G₂.perm) z23₁ z23₂ z24₁ z24₂

end

end VG.Proof.AesCcm.AArch64
