module

public import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.TCB.AArch64.Target

/-!
# The AArch64 taint analyses with statics are monotone

`AArch64.taint` and `AArch64.taintS L` are monotone along their order (with
more registers public on entry, every step succeeds, with more registers
public after it) and have frames (`Taint.LeFrame`), so `taint_summary` can
summarize code analysed with either once for all of its callers.
-/

@[expose] public section

namespace VG.AArch64.Taint

theorem stepS_mono {L : List String} {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true)
    (hs : stepS L τ i = some τ') : ∃ σ', stepS L σ i = some σ' ∧ τ'.subset σ' = true := by
  unfold stepS at hs ⊢
  split at hs
  · split at hs
    · rename_i hn
      cases hs; exact ⟨_, by simp only [hn, ↓reduceIte], set_mono h _ id⟩
    · rename_i hn
      simp only [hn, ↓reduceIte]; exact step_mono i h hs
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

theorem pop_keeps {F Φ σ σ' : T} (i : Instr) (hk : keepsI F i = true) (hΦF : Φ.subset F = true)
    (hΦ : Φ.subset σ = true) (hs : pop σ i = some σ') : Φ.subset σ' = true := by
  cases i <;> simp only [pop, reduceCtorEq, Option.some.injEq] at hs <;> subst hs
  · simp only [keepsI, gprDst, Bool.not_eq_true'] at hk
    exact RegSet.subset_erase_of hΦF hΦ hk
  · exact hΦ

theorem push_keeps {Φ σ σ' : T} (i : Instr) (hΦ : Φ.subset σ = true) (hs : push σ i = some σ') :
    Φ.subset σ' = true := by
  cases i <;> simp only [push, reduceCtorEq, Option.some.injEq] at hs <;> subst hs <;> exact hΦ

/-- A call writes `x16`, `x17` and `x30`. -/
def keepsCall (F : T) : Bool := !F.mem .x16 && !F.mem .x17 && !F.mem .x30

theorem keepsI_empty (i : Instr) : keepsI RegSet.empty i = true := by
  have h : ∀ d : Reg, (RegSet.empty : RegSet Reg).mem d = false := fun d => by
    simp [RegSet.mem, RegSet.empty]
  simp only [keepsI]
  split
  · rw [h, h]; rfl
  · split
    · rw [h]; rfl
    · rfl

theorem call_keeps {F Φ σ σ' : T} (hk : keepsCall F = true) (hΦF : Φ.subset F = true)
    (hΦ : Φ.subset σ = true) (hs : AArch64.taint.call σ = some σ') : Φ.subset σ' = true := by
  cases hs
  simp only [keepsCall, Bool.and_eq_true, Bool.not_eq_true'] at hk
  exact RegSet.subset_erase_of hΦF (RegSet.subset_erase_of hΦF
    (RegSet.subset_erase_of hΦF hΦ hk.1.1) hk.1.2) hk.2

end VG.AArch64.Taint

namespace VG.AArch64

open VG.Taint in
/-- The analysis of `taint` is monotone, with the meet as frames. -/
instance : LeFrame taint where
  le_right {_ b} _ := RegSet.subset_refl b
  le_trans h₁ h₂ := RegSet.subset_trans h₁ h₂
  step i h hs := Taint.step_mono i h hs
  condPub c h hc := Taint.condPub_mono c h hc
  meet h₁ h₂ := RegSet.inter_mono h₁ h₂
  call h hs := Taint.call_mono h hs
  ret h hs := by cases hs; exact ⟨_, rfl, h⟩
  push i h hs := Taint.push_mono i h hs
  pop i h hs := Taint.pop_mono i h hs
  join a b := a.union b
  bot := RegSet.empty
  join_lub ha hb :=
    ⟨RegSet.subset_union_left _ _, RegSet.subset_union_right _ _, RegSet.union_subset ha hb⟩
  frameOf a F := a.inter F
  frame_le_left _ _ := RegSet.inter_subset_left _ _
  frame_le_right _ _ _ := RegSet.inter_subset_right _ _
  frame_mono _ h := RegSet.inter_mono h (RegSet.subset_refl _)
  le_frame hb hc := RegSet.subset_inter hb hc
  le_meet hb hc := RegSet.subset_inter hb hc
  bot_le _ := RegSet.empty_subset _
  bot_valid := RegSet.subset_refl _
  keeps := Taint.keepsI
  keepsCall := Taint.keepsCall
  keeps_bot := Taint.keepsI_empty
  keepsCall_bot := rfl
  step_keeps i hk hΦF hΦ hs := Taint.step_keeps i hk hΦF hΦ hs
  call_keeps hk hΦF hΦ hs := Taint.call_keeps hk hΦF hΦ hs
  ret_keeps _ _ hΦ hs := by cases hs; exact hΦ
  push_keeps i _ _ hΦ hs := Taint.push_keeps i hΦ hs
  pop_keeps i hk hΦF hΦ hs := Taint.pop_keeps i hk hΦF hΦ hs

open VG.Taint in
/-- The analysis of `taintS L` is `taint`'s, but for the addresses of the
statics of `L`, which it makes public: monotone, with the meet as frames. -/
instance (L : List String) : LeFrame (taintS L) where
  le_right {_ b} _ := RegSet.subset_refl b
  le_trans h₁ h₂ := RegSet.subset_trans h₁ h₂
  step i h hs := Taint.stepS_mono i h hs
  condPub c h hc := Taint.condPub_mono c h hc
  meet h₁ h₂ := RegSet.inter_mono h₁ h₂
  call h hs := Taint.call_mono h hs
  ret h hs := by cases hs; exact ⟨_, rfl, h⟩
  push i h hs := Taint.push_mono i h hs
  pop i h hs := Taint.pop_mono i h hs
  join a b := a.union b
  bot := RegSet.empty
  join_lub ha hb :=
    ⟨RegSet.subset_union_left _ _, RegSet.subset_union_right _ _, RegSet.union_subset ha hb⟩
  frameOf a F := a.inter F
  frame_le_left _ _ := RegSet.inter_subset_left _ _
  frame_le_right _ _ _ := RegSet.inter_subset_right _ _
  frame_mono _ h := RegSet.inter_mono h (RegSet.subset_refl _)
  le_frame hb hc := RegSet.subset_inter hb hc
  le_meet hb hc := RegSet.subset_inter hb hc
  bot_le _ := RegSet.empty_subset _
  bot_valid := RegSet.subset_refl _
  keeps := Taint.keepsI
  keepsCall := Taint.keepsCall
  keeps_bot := Taint.keepsI_empty
  keepsCall_bot := rfl
  step_keeps i hk hΦF hΦ hs := Taint.stepS_keeps i hk hΦF hΦ hs
  call_keeps hk hΦF hΦ hs := Taint.call_keeps hk hΦF hΦ hs
  ret_keeps _ _ hΦ hs := by cases hs; exact hΦ
  push_keeps i _ _ hΦ hs := Taint.push_keeps i hΦ hs
  pop_keeps i hk hΦF hΦ hs := Taint.pop_keeps i hk hΦF hΦ hs

end VG.AArch64
