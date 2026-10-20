module

import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Cond
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Cond
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase

/-!
# AES-GCM `seal_split`'s path for TLS records: the condition

Untrusted: everything here is checked by Lean. `Fast.cond` leaves ZF clear
iff the path applies: a 12-byte nonce, at most 16 bytes of additional data
and at least 256 bytes of text, or any text with `any` (`cond_ok`), and takes
the same branches in two runs with the same lengths (`cond_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Fast
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Short (CondS CondKeep condB1_ok eval_ne eval_ae rel_next)

/-- When the path applies. -/
abbrev IsFast (nl al n : Nat) (any : Bool := false) : Prop := nl = 12 ∧ al < 17 ∧ (any = true ∨ 256 ≤ n)

/-- A length in `W` at `d` compared with `k`. -/
theorem condLen_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) {d v k : Nat}
    (hd : d = 184 ∨ d = 208) (hv : s.mem.readW (W + BitVec.ofNat 64 d) 64 = BitVec.ofNat 64 v) (hv' : v < 2 ^ 64)
    (hk : k < 2 ^ 31) :
    WP isa (.block [.mov .rcx (.mem (at_ .r15 d)), .alu .cmp .rcx (imm k)]) s fun t =>
      t.cf = some (decide (v < k)) ∧ t.gpr .rax = s.gpr .rax ∧ CondKeep s t := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    in_left (in_off h.w (by rcases hd with rfl | rfl <;> decide) (by decide))
  have h15 := h.r15
  obtain ⟨s₃, run₃, cx₃, ax₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .rcx (.mem (at_ .r15 d))] s = some s₃ ∧
      s₃.gpr .rcx = BitVec.ofNat 64 v ∧ s₃.gpr .rax = s.gpr .rax ∧ CondKeep s s₃ := by
    refine ⟨_, by xrun [h15, hv, r₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, b]
    all_goals rfl
  obtain ⟨s₄, run₄, -, cf₄, g₄, m₄, rd₄, wr₄⟩ := cmpImm_ok s₃ .rcx cx₃ hv' hk
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, cf₄, by rw [g₄, ax₃],
    k₃.trans ⟨fun r _ _ _ => by rw [g₄], m₄, rd₄, wr₄⟩⟩⟩)

/-- `cond`: ZF clear iff the path applies, with `rbp` the nonce's length and
the lengths of the additional data and the text in `W`. -/
theorem cond_ok {s : State} {W : Addr} {nl al n : Nat} {any : Bool} (h : CondS W nl al n s) (hnl : nl < 2 ^ 64)
    (hal : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    WP isa (cond any) s fun s' => s'.zf = some (decide ¬IsFast nl al n any) ∧ CondKeep s s' := by
  refine WP.seq (WP.mono (condB1_ok h hnl) fun s₂ ⟨zf₂, ax₂, k₂⟩ => ?_)
  -- `rax := 1` iff the path applies.
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .rax = BitVec.ofNat 64 (if IsFast nl al n any then 1 else 0) ∧
      CondKeep s s₃) (WP.ite (!decide (nl = 12)) (eval_ne zf₂) (fun h12 => ?_) (fun h12 => ?_)) fun s₃ ⟨ax₃, k₃⟩ => ?_)
  · have h12 : nl ≠ 12 := by simpa using h12
    refine WP.block_nil ⟨?_, k₂⟩
    rw [ax₂]
    simp [IsFast, h12]
  · have h12 : nl = 12 := by simpa using h12
    refine WP.seq (WP.mono (condLen_ok (h.keep k₂) (.inl rfl) (by rw [k₂.mem]; exact h.alen) hal
      (show 17 < 2 ^ 31 by decide)) fun s₄ ⟨cf₄, ax₄, k₄⟩ => ?_)
    rw [ax₂] at ax₄
    refine WP.ite (!decide (al < 17)) (eval_ae cf₄) (fun h5 => ?_) (fun h5 => ?_)
    · have h5 : ¬al < 17 := by simpa using h5
      refine WP.block_nil ⟨?_, k₂.trans k₄⟩
      rw [ax₄]
      simp [IsFast, h5]
    · have h5 : al < 17 := by simpa using h5
      cases any
      · simp only [condLen, Bool.false_eq_true, ↓reduceIte]
        refine WP.seq (WP.mono (condLen_ok ((h.keep k₂).keep k₄) (.inr rfl)
          (by rw [k₄.mem, k₂.mem]; exact h.len) hn (show 256 < 2 ^ 31 by decide)) fun s₆ ⟨cf₆, ax₆, k₆⟩ => ?_)
        rw [ax₄] at ax₆
        refine WP.ite (decide (n < 256)) (eval_b cf₆) (fun h2 => ?_) (fun h2 => ?_)
        · have h2 : n < 256 := by simpa using h2
          exact WP.block_nil ⟨by simp [ax₆, IsFast, show ¬256 ≤ n by omega], k₂.trans (k₄.trans k₆)⟩
        · have h2 : ¬n < 256 := by simpa using h2
          have hs : IsFast nl al n false := ⟨h12, h5, .inr (by omega)⟩
          refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
          · have e : (if IsFast nl al n false then 1 else 0) = 1 := ite_eq_left_iff.mpr fun h => absurd hs h
            rw [e]
            simp [gpr_setReg]
          · exact k₂.trans (k₄.trans (k₆.trans ⟨fun r a _ _ => by simp [gpr_setReg, a], rfl, rfl, rfl⟩))
      · simp only [condLen, ↓reduceIte]
        have hs : IsFast nl al n true := ⟨h12, h5, .inl rfl⟩
        refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
        · have e : (if IsFast nl al n true then 1 else 0) = 1 := ite_eq_left_iff.mpr fun h => absurd hs h
          rw [e]
          simp [gpr_setReg]
        · exact k₂.trans (k₄.trans ⟨fun r a _ _ => by simp [gpr_setReg, a], rfl, rfl, rfl⟩)
  -- `test rax, rax`.
  refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
  · rw [zf_arithFlags, ax₃]
    split <;> rename_i h <;> simp [h]
  · exact k₃.trans ⟨fun r _ _ _ => by simp [gpr_arithFlags], rfl, rfl, rfl⟩

/-- `cond` in two runs with the same lengths: the same branches. -/
theorem cond_rel {W : Addr} {nl al n : Nat} {F₁ F₂ : State → Prop}
    (h₁ : ∀ s, F₁ s → CondS W nl al n s) (h₂ : ∀ s, F₂ s → CondS W nl al n s)
    (hnl : nl < 2 ^ 64) (hal : al < 2 ^ 64) (hn : n < 2 ^ 64) {any : Bool} :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (cond any) fun _ _ => True := by
  have w₁ : ∀ {F : State → Prop}, (∀ s, F s → CondS W nl al n s) → ∀ s, F s →
      WP isa (.block [.mov32 .rax (imm 0), .alu .cmp .rbp (imm 12)]) s fun t =>
        t.zf = some (decide (nl = 12)) ∧ CondS W nl al n t := fun hF s h =>
    WP.mono (condB1_ok (hF s h) hnl) fun _ ⟨z, _, k⟩ => ⟨z, (hF s h).keep k⟩
  have b1 := rel_next (rel_taint (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) [.rbp] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h₁ _ h.1).rbp, (h₂ _ h.2).rbp]) ⟨_, by taint_decide⟩)
    (w₁ h₁) (w₁ h₂)
  have last := rel_taint (P := fun _ _ => True) (c := .block [.alu .test .rax (.reg .rax)]) []
    (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  have none := rel_taint (P := fun _ _ => True) (c := .block []) [] (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  have one := rel_taint (P := fun _ _ => True) (c := .block [.mov32 .rax (imm 1)]) []
    (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  refine RelCT.seq b1 (RelCT.seq (RelCT.ite (fun _ _ h => by
      rw [eval_ne h.1.1, eval_ne h.2.1]) (none.mono (fun _ _ _ => trivial) fun _ _ h => h) ?_)
    (last.mono (fun _ _ _ => trivial) fun _ _ h => h))
  -- The additional data's length compared with 17.
  have w₂ : ∀ s, (s.zf = some (decide (nl = 12)) ∧ CondS W nl al n s) →
      WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .cmp .rcx (imm 17)]) s fun t =>
        t.cf = some (decide (al < 17)) ∧ CondS W nl al n t :=
    fun s h => WP.mono (condLen_ok h.2 (.inl rfl) h.2.alen hal (by decide)) fun _ ⟨c, _, k⟩ => ⟨c, h.2.keep k⟩
  have b2 := rel_next (rel_taint (P := fun s₁ s₂ =>
      (s₁.zf = some (decide (nl = 12)) ∧ CondS W nl al n s₁) ∧ (s₂.zf = some (decide (nl = 12)) ∧ CondS W nl al n s₂))
      [.r15] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.r15, h.2.2.r15]) ⟨_, by taint_decide⟩) w₂ w₂
  refine RelCT.seq (b2.mono (fun _ _ h => h.1) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => (eval_ae h.1.1).trans (eval_ae h.2.1).symm)
      (none.mono (fun _ _ _ => trivial) fun _ _ h => h) ?_)
  cases any
  case true =>
    simp only [condLen, ↓reduceIte]
    exact one.mono (fun _ _ _ => trivial) fun _ _ h => h
  simp only [condLen, Bool.false_eq_true, ↓reduceIte]
  -- The text's length compared with 256.
  have w₃ : ∀ s, (s.cf = some (decide (al < 17)) ∧ CondS W nl al n s) →
      WP isa (.block [.mov .rcx (.mem (at_ .r15 lenO)), .alu .cmp .rcx (imm 256)]) s fun t =>
        t.cf = some (decide (n < 256)) :=
    fun s h => WP.mono (condLen_ok h.2 (.inr rfl) h.2.len hn (by decide)) fun _ ⟨c, _⟩ => c
  have b3 := rel_next (rel_taint (P := fun s₁ s₂ =>
      (s₁.cf = some (decide (al < 17)) ∧ CondS W nl al n s₁) ∧ (s₂.cf = some (decide (al < 17)) ∧ CondS W nl al n s₂))
      [.r15] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.r15, h.2.2.r15]) ⟨_, by taint_decide⟩) w₃ w₃
  refine RelCT.seq (b3.mono (fun _ _ h => h.1) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => (eval_b h.1).trans (eval_b h.2).symm)
      (none.mono (fun _ _ _ => trivial) fun _ _ h => h) (one.mono (fun _ _ _ => trivial) fun _ _ h => h))

end VG.Proof.AesGcm.X86_64.Fast
