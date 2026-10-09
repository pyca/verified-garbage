import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# Summaries for the x86 SIMD taint analysis

`sseTaint` shares `taint`'s domain and every rule but `step`, so it is
monotone along the same order (`LeR`) with the same frames of registers:
its SIMD steps write no general-purpose register or flag, and check only
that a base register is public (`memPub`), which more public registers keep.
-/

namespace VG.X86.SseTaint

open VG.X86.Taint

private theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem memPub_upd {τ : T} {r : RegSet Reg} {f : Bool} {sl : List (Nat × Nat × Nat)}
    (hr : τ.regs.subset r = true) {m : MemOp} (h : memPub τ m = true) :
    memPub (upd τ r f sl) m = true := pub_upd hr h

theorem step_upd {τ : T} {r : RegSet Reg} {f : Bool} {sl : List (Nat × Nat × Nat)}
    (hr : τ.regs.subset r = true) (hf : τ.flags = true → f = true)
    (hsl : ∀ x ∈ τ.slots, x ∈ sl) (i : Instr) {τ' : T} (hs : step τ i = some τ') :
    ∃ σ', step (upd τ r f sl) i = some σ' ∧ LeR τ' σ' := by
  have hst : ∀ m w, storeStepK τ m w false [] = some τ' →
      ∃ σ', storeStepK (upd τ r f sl) m w false [] = some σ' ∧ LeR τ' σ' := fun m w h => by
    rw [storeStepK_eq] at h ⊢; exact storeStep_upd hr hf hsl m w id [] h
  have hld : ∀ m, (if memPub τ m = true then some τ else none) = some τ' →
      ∃ σ', (if memPub (upd τ r f sl) m = true then some (upd τ r f sl) else none) = some σ' ∧
        LeR τ' σ' := fun m h => by
    split at h <;> [rename_i hm; cases h]
    cases h
    exact ⟨_, ite_t (memPub_upd hr hm), leR_upd hr hf hsl⟩
  cases i with
  | movdquLoad _ m => exact hld m hs
  | movqLoad _ m => exact hld m hs
  | movdquStore m _ => exact hst m 16 hs
  | movqStore m _ => exact hst m 8 hs
  | mmxStore m _ => exact hst m 8 hs
  | xop _ =>
    simp only [step, Option.some.injEq] at hs ⊢
    subst hs
    exact ⟨_, rfl, leR_upd hr hf hsl⟩
  | mop op =>
    simp only [step] at hs ⊢
    split at hs <;> [rename_i hm; cases hs]
    cases hs
    have hm' : mopOk (upd τ r f sl) op = true := by
      cases op with
      | bin _ _ src | movq _ src =>
        cases src with
        | mem m => exact memPub_upd hr hm
        | _ => rfl
      | _ => rfl
    exact ⟨_, ite_t hm', leR_upd hr hf hsl⟩
  | _ =>
    simp only [step] at hs ⊢
    rw [stepK_eq] at hs ⊢
    exact Taint.step_upd hr hf hsl _ hs

theorem LeR.step {τ σ τ' : T} (h : LeR τ σ) (i : Instr) (hs : step τ i = some τ') :
    ∃ σ', step σ i = some σ' ∧ LeR τ' σ' := by
  rw [h.shape]; exact step_upd h.regs h.flags h.slots i hs

/-- A step keeps public the registers and flags the instruction does not write. -/
theorem step_keeps {F Φ σ σ' : T} (i : Instr) (hk : keepsI F i = true) (hΦF : frLe Φ F = true)
    (hΦ : frLe Φ σ = true) (hs : step σ i = some σ') : frLe Φ σ' = true := by
  have hst : ∀ m w, storeStepK σ m w false [] = some σ' → frLe Φ σ' = true := fun m w h => by
    rw [storeStepK_eq] at h
    unfold storeStep at h
    split at h <;> [skip; cases h]
    cases h; exact hΦ
  have hld : ∀ m, (if memPub σ m = true then some σ else none) = some σ' → frLe Φ σ' = true :=
    fun m h => by
      split at h <;> [skip; cases h]
      cases h; exact hΦ
  cases i with
  | movdquLoad _ m => exact hld m hs
  | movqLoad _ m => exact hld m hs
  | movdquStore m _ => exact hst m 16 hs
  | movqStore m _ => exact hst m 8 hs
  | mmxStore m _ => exact hst m 8 hs
  | xop _ =>
    simp only [step, Option.some.injEq] at hs
    subst hs; exact hΦ
  | mop op =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    cases hs; exact hΦ
  | _ =>
    simp only [step] at hs
    rw [stepK_eq] at hs
    exact step_keeps' _ hk hΦF hΦ hs

end VG.X86.SseTaint

namespace VG.X86

private abbrev I : VG.Taint.Frame taint := inferInstance

open VG.X86.Taint in
/-- The SIMD analysis is monotone along `LeR`, with frames of registers, as
`taint` is. -/
instance : VG.Taint.Frame sseTaint :=
  { R := I.R
    R_trans := I.R_trans
    R_right := I.R_right
    le_R := I.le_R
    step := fun {τ σ τ'} i h hs => by
      have hs : SseTaint.step τ i = some τ' := hs
      obtain ⟨σ', h₁, h₂⟩ := SseTaint.LeR.step (leR_iff.mp h) i hs
      exact ⟨σ', h₁, leR_iff.mpr h₂⟩
    condPub := I.condPub
    meet := I.meet
    call := I.call
    ret := I.ret
    push := I.push
    pop := I.pop
    join := I.join
    bot := I.bot
    frameOf := I.frameOf
    Fr := I.Fr
    Fr_trans := I.Fr_trans
    Fr_R := I.Fr_R
    join_hint := I.join_hint
    join_R := I.join_R
    frame_le_left := I.frame_le_left
    frame_le_right := I.frame_le_right
    frame_mono := I.frame_mono
    le_frame := I.le_frame
    le_meet := I.le_meet
    bot_le := I.bot_le
    bot_valid := I.bot_valid
    keeps := I.keeps
    keepsCall := I.keepsCall
    keeps_bot := I.keeps_bot
    keepsCall_bot := I.keepsCall_bot
    step_keeps := fun i hk hΦF hΦ hs => SseTaint.step_keeps i hk hΦF hΦ hs
    call_keeps := I.call_keeps
    ret_keeps := I.ret_keeps
    push_keeps := I.push_keeps
    pop_keeps := I.pop_keeps }

end VG.X86
