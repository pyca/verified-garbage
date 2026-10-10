import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Framework.AArch64.TaintMono

/-!
# AArch64 taint tracking with the addresses of statics is monotone

`taintS L` is `taint` with the register `adrSym` sets to the address of a
static of `L` public: with more registers public on entry, every step still
succeeds, with more registers public after it, and a step that writes no
register of a frame `F` keeps what of `F` was public (`Taint.LeFrame`), so
checks by `taintS L` can use summaries (`taint_summary`, `taint_decide_sum`).
-/

namespace VG.AArch64.Taint

theorem stepS_mono {L : List String} {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true)
    (hs : stepS L τ i = some τ') : ∃ σ', stepS L σ i = some σ' ∧ τ'.subset σ' = true := by
  unfold stepS at hs ⊢
  split at hs
  · rename_i d n _
    split at hs
    · rename_i hn
      cases hs
      exact ⟨_, by simp only [hn, ↓reduceIte], set_mono h d id⟩
    · rename_i hn
      simp only [hn, ↓reduceIte]
      exact step_mono i h hs
  · exact step_mono i h hs

theorem stepS_keeps {L : List String} {F Φ σ σ' : T} (i : Instr) (hk : keepsI F i = true)
    (hΦF : Φ.subset F = true) (hΦ : Φ.subset σ = true) (hs : stepS L σ i = some σ') :
    Φ.subset σ' = true := by
  unfold stepS at hs
  split at hs
  · rename_i d n hsym
    split at hs
    · cases hs
      obtain rfl := Instr.sym_eq hsym
      simp only [keepsI, gprDst, Bool.not_eq_true'] at hk
      exact set_keeps hΦF hΦ hk _
    · exact step_keeps i hk hΦF hΦ hs
  · exact step_keeps i hk hΦF hΦ hs

/-- A call writes `x16`, `x17` and `x30`. -/
def keepsCallS (F : T) : Bool := !F.mem .x16 && !F.mem .x17 && !F.mem .x30

end VG.AArch64.Taint

namespace VG.AArch64

open VG.AArch64.Taint in
instance (L : List String) : VG.Taint.LeFrame (taintS L) where
  le_right {_ b} _ := RegSet.subset_refl b
  le_trans h₁ h₂ := RegSet.subset_trans h₁ h₂
  step i h hs := stepS_mono i h hs
  condPub c h hc := condPub_mono c h hc
  meet h₁ h₂ := RegSet.inter_mono h₁ h₂
  call h hs := call_mono h hs
  ret h hs := by cases hs; exact ⟨_, rfl, h⟩
  push i h hs := push_mono i h hs
  pop i h hs := pop_mono i h hs
  join a b := a.union b
  bot := RegSet.empty
  join_lub ha hb :=
    ⟨RegSet.subset_union_left _ _, RegSet.subset_union_right _ _, RegSet.union_subset ha hb⟩
  frameOf a b := a.inter b
  frame_le_left _ _ := RegSet.inter_subset_left _ _
  frame_le_right _ _ _ := RegSet.inter_subset_right _ _
  frame_mono _ h := RegSet.inter_mono h (RegSet.subset_refl _)
  le_frame hb hc := RegSet.subset_inter hb hc
  le_meet hb hc := RegSet.subset_inter hb hc
  bot_le _ := RegSet.empty_subset _
  bot_valid := RegSet.subset_refl _
  keeps := keepsI
  keepsCall := keepsCallS
  keeps_bot i := by
    have h : ∀ d : Reg, (RegSet.empty : RegSet Reg).mem d = false := fun d => by
      simp [RegSet.mem, RegSet.empty]
    simp only [keepsI]
    split
    · rw [h]; rfl
    · rfl
  keepsCall_bot := rfl
  step_keeps i hk hΦF hΦ hs := stepS_keeps i hk hΦF hΦ hs
  call_keeps {F Φ σ σ'} hk hΦF hΦ hs := by
    have hs : AArch64.taint.call σ = some σ' := hs
    cases hs
    simp only [keepsCallS, Bool.and_eq_true, Bool.not_eq_true'] at hk
    exact RegSet.subset_erase_of hΦF (RegSet.subset_erase_of hΦF
      (RegSet.subset_erase_of hΦF hΦ hk.1.1) hk.1.2) hk.2
  ret_keeps _ _ hΦ hs := by cases hs; exact hΦ
  push_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : Taint.push σ i = some σ' := hs
    cases i <;> simp only [Taint.push, reduceCtorEq] at hs <;> cases hs <;> exact hΦ
  pop_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : Taint.pop σ i = some σ' := hs
    cases i <;> simp only [Taint.pop, reduceCtorEq] at hs <;> cases hs
    · simp only [keepsI, gprDst, Bool.not_eq_true'] at hk
      exact RegSet.subset_erase_of hΦF hΦ hk
    · exact hΦ

end VG.AArch64
