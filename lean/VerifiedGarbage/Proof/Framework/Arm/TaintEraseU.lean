module

public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal

/-!
# Taint tracking for ARMv7 with `umaal`: code without its offsets

`taintU`, as `taint` (`Arm/TaintErase.lean`), reads neither the offsets of
loads and stores nor the immediates of `movw` from a taint that knows no
region bases and no stack arguments: `umaal` has neither, and leaves such a
taint so (`checkU_eraseOff`).
-/

-- separate module: the analysis of `taintU`, apart from the arithmetic that first uses it

@[expose] public section

namespace VG.Arm

namespace Taint

/-- `taintU`'s step is `stepU`'s (`stepKeepU_eq`). -/
theorem taintU_step (τ : T) (i : Instr) : taintU.step τ i = stepU τ i :=
  congrFun (congrFun stepKeepU_eq τ) i

theorem stepU_eraseOff {τ : T} (h : NoBase τ) (i : Instr) : stepU τ i.eraseOff = stepU τ i := by
  cases i <;> simp only [stepU, Instr.eraseOff]
  all_goals first
    | exact step_eraseOff h (.ldr _ _ _) | exact step_eraseOff h (.str _ _ _)
    | exact step_eraseOff h (.ldrb _ _ _) | exact step_eraseOff h (.strb _ _ _)
    | exact step_eraseOff h (.movw _ _)

theorem stepU_noBase {τ τ' : T} (h : NoBase τ) {i : Instr} (hs : stepU τ i = some τ') : NoBase τ' := by
  cases i
  case umaal lo hi n m =>
    obtain rfl : secret2 τ lo hi = τ' := Option.some.inj hs
    exact ⟨by simp only [secret2, h.1, List.filter_nil], h.2⟩
  all_goals
    simp only [stepU] at hs
    exact step_noBase h hs

private theorem bind_congr {α β : Type} {o : Option α} {f g : α → Option β}
    (h : ∀ a, o = some a → f a = g a) : o.bind f = o.bind g := by
  cases o with
  | none => rfl
  | some a => exact h a rfl

theorem checkBlockU_noBase {τ τ' : T} (h : NoBase τ) {is : List Instr}
    (hc : taintU.checkBlock τ is = some τ') : NoBase τ' := by
  induction is generalizing τ with
  | nil => cases hc; exact h
  | cons i is ih =>
    have hc : (taintU.step τ i).bind (taintU.checkBlock · is) = some τ' := hc
    rw [taintU_step] at hc
    obtain ⟨σ, hσ, hc⟩ := Option.bind_eq_some_iff.mp hc
    exact ih (stepU_noBase h hσ) hc

theorem checkBlockU_eraseOff {τ : T} (h : NoBase τ) (is : List Instr) :
    taintU.checkBlock τ (is.map Instr.eraseOff) = taintU.checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (taintU.step τ i.eraseOff).bind (taintU.checkBlock · _) = (taintU.step τ i).bind (taintU.checkBlock · _)
    rw [taintU_step, taintU_step, stepU_eraseOff h]
    exact bind_congr fun σ hσ => ih (stepU_noBase h hσ)

theorem checkChunksU_noBase {chunkSize : Nat} {τ τ' : T} (h : NoBase τ) {is : List Instr} {ms : List T}
    (hc : taintU.checkChunks chunkSize τ is ms = some τ') : NoBase τ' := by
  induction ms generalizing τ is with
  | nil => exact checkBlockU_noBase h hc
  | cons m ms ih =>
    have hc : (taintU.checkBlock τ (is.take chunkSize)).bind (fun τ' =>
        if taintU.le m τ' then taintU.checkChunks chunkSize m (is.drop chunkSize) ms else none) = some τ' := by
      simpa only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq] using hc
    obtain ⟨σ, hσ, hc⟩ := Option.bind_eq_some_iff.mp hc
    split at hc
    · rename_i hl
      exact ih (le_noBase hl (checkBlockU_noBase h hσ)) hc
    · cases hc

theorem checkChunksU_eraseOff {chunkSize : Nat} {τ : T} (h : NoBase τ) (is : List Instr) (ms : List T) :
    taintU.checkChunks chunkSize τ (is.map Instr.eraseOff) ms = taintU.checkChunks chunkSize τ is ms := by
  induction ms generalizing τ is with
  | nil => exact checkBlockU_eraseOff h is
  | cons m ms ih =>
    simp only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq, ← List.map_take, ← List.map_drop, checkBlockU_eraseOff h]
    refine bind_congr fun σ hσ => ?_
    split
    · rename_i hl
      exact ih (le_noBase hl (checkBlockU_noBase h hσ)) _
    · rfl

theorem checkU_noBase : ∀ (c : Prog isa) {τ τ' : T} {hc : VG.Taint.Hint taintU.T}, NoBase τ →
    taintU.check τ c hc = some τ' → NoBase τ'
  | .block is, τ, τ', hc, h, e => by
    cases hc <;> first | exact checkChunksU_noBase h e | cases e
  | .seq a b, τ, τ', hc, h, e => by
    cases hc with
    | seq mid h₁ h₂ =>
      have e : (taintU.check τ a h₁).bind (fun τ' =>
          if taintU.le mid τ' then taintU.check mid b h₂ else none) = some τ' := e
      obtain ⟨σ, hσ, e⟩ := Option.bind_eq_some_iff.mp e
      split at e
      · rename_i hl
        exact checkU_noBase b (le_noBase hl (checkU_noBase a h hσ)) e
      · cases e
    | _ => cases e
  | .ite c t f, τ, τ', hc, h, e => by
    cases hc with
    | ite h₁ h₂ =>
      have e : (if taintU.condPub τ c then
          (taintU.check τ t h₁).bind fun τ₁ => (taintU.check τ f h₂).map fun τ₂ => taintU.meet τ₁ τ₂
          else none) = some τ' := e
      split at e
      · obtain ⟨σ₁, hσ₁, e⟩ := Option.bind_eq_some_iff.mp e
        obtain ⟨σ₂, -, rfl⟩ := Option.map_eq_some_iff.mp e
        exact meet_noBase (checkU_noBase t h hσ₁)
      · cases e
    | _ => cases e
  | .loop body c, τ, τ', hc, h, e => by
    cases hc with
    | loop σ hb =>
      have e : (if taintU.le σ τ then
          (taintU.check σ body hb).bind fun σ' => if taintU.le σ σ' && taintU.condPub σ' c then some σ'
            else none
          else none) = some τ' := e
      split at e
      · rename_i hl
        obtain ⟨σ', hσ', e⟩ := Option.bind_eq_some_iff.mp e
        split at e
        · cases e; exact checkU_noBase body (le_noBase hl h) hσ'
        · cases e
      · cases e
    | _ => cases e
  | .call n body, τ, τ', hc, h, e => by
    cases hc with
    | call hb =>
      have e : (taintU.check (callStep τ) body hb).bind (fun τ₂ => some τ₂) = some τ' := e
      obtain ⟨σ', hσ', e⟩ := Option.bind_eq_some_iff.mp e
      cases e
      exact checkU_noBase body (callStep_noBase h) hσ'
    | _ => cases e
  | .frame p body q, τ, τ', hc, h, e => by
    cases hc with
    | frame hb => cases e
    | _ => cases e
  | .icall .., τ, τ', hc, h, e => by cases hc <;> cases e

theorem checkU_eraseOff : ∀ (c : Prog isa) {τ : T} (hc : VG.Taint.Hint taintU.T), NoBase τ →
    taintU.check τ (Code.eraseOff c) hc = taintU.check τ c hc
  | .block is, τ, hc, h => by
    cases hc <;> first | rfl | exact checkChunksU_eraseOff h is _
  | .seq a b, τ, hc, h => by
    cases hc with
    | seq mid h₁ h₂ =>
      show (taintU.check τ (Code.eraseOff a) h₁).bind _ = (taintU.check τ a h₁).bind _
      rw [checkU_eraseOff a h₁ h]
      refine bind_congr fun σ hσ => ?_
      split
      · rename_i hl
        exact checkU_eraseOff b h₂ (le_noBase hl (checkU_noBase a h hσ))
      · rfl
    | _ => rfl
  | .ite c t f, τ, hc, h => by
    cases hc with
    | ite h₁ h₂ =>
      show (if taintU.condPub τ c then (taintU.check τ (Code.eraseOff t) h₁).bind fun τ₁ =>
          (taintU.check τ (Code.eraseOff f) h₂).map fun τ₂ => taintU.meet τ₁ τ₂ else none) = _
      rw [checkU_eraseOff t h₁ h, checkU_eraseOff f h₂ h]; rfl
    | _ => rfl
  | .loop body c, τ, hc, h => by
    cases hc with
    | loop σ hb =>
      show (if taintU.le σ τ then _ else none) = (if taintU.le σ τ then _ else none)
      split
      · rename_i hl
        rw [checkU_eraseOff body hb (le_noBase hl h)]
      · rfl
    | _ => rfl
  | .call n body, τ, hc, h => by
    cases hc with
    | call hb =>
      show ((some (callStep τ)).bind fun τ₁ => (taintU.check τ₁ (Code.eraseOff body) hb).bind taintU.ret) =
        (some (callStep τ)).bind fun τ₁ => (taintU.check τ₁ body hb).bind taintU.ret
      rw [Option.bind_some, Option.bind_some, checkU_eraseOff body hb (callStep_noBase h)]
    | _ => rfl
  | .frame p body q, τ, hc, h => by
    cases hc <;> rfl
  | .icall .., τ, hc, h => by
    cases hc <;> rfl

end Taint

end VG.Arm
