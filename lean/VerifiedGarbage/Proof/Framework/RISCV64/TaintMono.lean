module

public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.RegSetOrder

/-!
# The RISC-V taint analyses are monotone

As on AArch64 (`Proof/Framework/AArch64/TaintSymMono.lean`): `RISCV64.taint`
and `RISCV64.taintSym L` are monotone along their order (with more registers
public on entry, every step succeeds, with more registers public after it)
and have frames (`Taint.LeFrame`), so `taint_summary` can summarize code
analysed with either once for all of its callers, and their checks can use
the summaries (`taint_decide_sum`).
-/

@[expose] public section

namespace VG

namespace RISCV64.Taint

theorem pub_mono {τ σ : T} (h : τ.subset σ = true) {r : Reg} (hr : pub τ r = true) :
    pub σ r = true := RegSet.mem_of_subset h hr

theorem set_mono {τ σ : T} (h : τ.subset σ = true) (d : Reg) {p q : Bool}
    (hpq : p = true → q = true) : (set τ d p).subset (set σ d q) = true := by
  unfold set
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact RegSet.erase_mono h d
  · exact RegSet.subset_trans (RegSet.erase_subset τ d)
      (RegSet.subset_trans h (RegSet.subset_insert σ d))
  · exact absurd (hpq rfl) Bool.false_ne_true
  · exact RegSet.insert_mono h d

theorem step_mono {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true) (hs : step τ i = some τ') :
    ∃ σ', step σ i = some σ' ∧ τ'.subset σ' = true := by
  have and2 : ∀ {a b : Reg}, (pub τ a && pub τ b) = true → (pub σ a && pub σ b) = true :=
    fun hab => by
      simp only [Bool.and_eq_true] at hab ⊢; exact ⟨pub_mono h hab.1, pub_mono h hab.2⟩
  cases i <;> simp only [step, reduceCtorEq] at hs ⊢
  all_goals first
    | (cases hs; exact ⟨_, rfl, set_mono h _ and2⟩)
    | (cases hs; exact ⟨_, rfl, set_mono h _ (pub_mono h)⟩)
    | (cases hs; exact ⟨_, rfl, set_mono h _ id⟩)
    | (split at hs <;> [rename_i hn; cases hs]
       cases hs
       exact ⟨_, by simp only [pub_mono h hn, ↓reduceIte]; rfl,
         (by first | exact set_mono h _ id | exact h)⟩)

theorem condPub_mono {τ σ : T} (c : Cond) (h : τ.subset σ = true) (hc : condPub τ c = true) :
    condPub σ c = true := by
  cases c <;> simp only [condPub, Bool.and_eq_true] at hc ⊢
  · exact pub_mono h hc
  · exact pub_mono h hc
  all_goals exact ⟨pub_mono h hc.1, pub_mono h hc.2⟩

theorem callErase_mono {τ σ : T} (h : τ.subset σ = true) :
    (callErase τ).subset (callErase σ) = true :=
  RegSet.erase_mono (RegSet.erase_mono (RegSet.erase_mono (RegSet.erase_mono (RegSet.erase_mono
    (RegSet.erase_mono (RegSet.erase_mono (RegSet.erase_mono h _) _) _) _) _) _) _) _

theorem push_mono {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true) (hs : push τ i = some τ') :
    ∃ σ', push σ i = some σ' ∧ τ'.subset σ' = true := by
  cases i <;> simp only [push, reduceCtorEq] at hs ⊢ <;> cases hs <;> exact ⟨_, rfl, h⟩

theorem pop_mono {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true) (hs : pop τ i = some τ') :
    ∃ σ', pop σ i = some σ' ∧ τ'.subset σ' = true := by
  cases i <;> simp only [pop, reduceCtorEq] at hs ⊢ <;> cases hs
  · exact ⟨_, rfl, RegSet.erase_mono h _⟩
  · exact ⟨_, rfl, h⟩

/-- The register an instruction writes, if any. -/
def gprDst : Instr → Option Reg
  | .add d .. | .sub d .. | .addw d .. | .subw d .. | .sltu d .. | .mul d .. | .mulhu d ..
  | .logic _ d .. | .addi d .. | .addiw d .. | .logicImm _ d .. | .li d _ | .lui d _
  | .shift _ _ d .. | .shiftReg _ _ d .. | .load _ d .. | .pop d | .addSp d _ | .lla d _ => some d
  | _ => none

/-- `i` writes no register of `F`. -/
def keepsI (F : T) (i : Instr) : Bool :=
  match gprDst i with
  | some d => !F.mem d
  | none => true

theorem set_keeps {Φ F σ : T} (hΦF : Φ.subset F = true) (hΦ : Φ.subset σ = true) {d : Reg}
    (hd : F.mem d = false) (p : Bool) : Φ.subset (set σ d p) = true := by
  unfold set
  cases p
  · exact RegSet.subset_erase_of hΦF hΦ hd
  · exact RegSet.subset_insert_of hΦ d

theorem step_keeps {F Φ σ σ' : T} (i : Instr) (hk : keepsI F i = true) (hΦF : Φ.subset F = true)
    (hΦ : Φ.subset σ = true) (hs : step σ i = some σ') : Φ.subset σ' = true := by
  cases i <;> simp only [step, reduceCtorEq] at hs <;>
    simp only [keepsI, gprDst, Bool.not_eq_true'] at hk
  all_goals first
    | (cases hs; exact set_keeps hΦF hΦ hk _)
    | (split at hs <;> [skip; cases hs]
       cases hs
       first | exact set_keeps hΦF hΦ hk _ | exact hΦ)

/-- `lla d n` of a static and the `li d, 0` it is analysed as write the same register. -/
theorem keepsI_symLi (L : List String) (F : T) (i : Instr) : keepsI F (i.symLi L) = keepsI F i := by
  cases i <;> simp only [Instr.symLi]
  split <;> rfl

theorem pop_keeps {F Φ σ σ' : T} (i : Instr) (hk : keepsI F i = true) (hΦF : Φ.subset F = true)
    (hΦ : Φ.subset σ = true) (hs : pop σ i = some σ') : Φ.subset σ' = true := by
  cases i <;> simp only [pop, reduceCtorEq, Option.some.injEq] at hs <;> subst hs
  · simp only [keepsI, gprDst, Bool.not_eq_true'] at hk
    exact RegSet.subset_erase_of hΦF hΦ hk
  · exact hΦ

theorem push_keeps {Φ σ σ' : T} (i : Instr) (hΦ : Φ.subset σ = true) (hs : push σ i = some σ') :
    Φ.subset σ' = true := by
  cases i <;> simp only [push, reduceCtorEq, Option.some.injEq] at hs <;> subst hs <;> exact hΦ

/-- A call writes `ra` and `t0`–`t6`. -/
def keepsCall (F : T) : Bool :=
  !F.mem .ra && !F.mem .t0 && !F.mem .t1 && !F.mem .t2 && !F.mem .t3 && !F.mem .t4 && !F.mem .t5 &&
    !F.mem .t6

theorem keepsI_empty (i : Instr) : keepsI RegSet.empty i = true := by
  have h : ∀ d : Reg, (RegSet.empty : RegSet Reg).mem d = false := fun d => by
    simp [RegSet.mem, RegSet.empty]
  simp only [keepsI]
  split
  · rw [h]; rfl
  · rfl

theorem callErase_keeps {F Φ σ : T} (hk : keepsCall F = true) (hΦF : Φ.subset F = true)
    (hΦ : Φ.subset σ = true) : Φ.subset (callErase σ) = true := by
  simp only [keepsCall, Bool.and_eq_true, Bool.not_eq_true'] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨hra, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hk
  exact RegSet.subset_erase_of hΦF (RegSet.subset_erase_of hΦF (RegSet.subset_erase_of hΦF
    (RegSet.subset_erase_of hΦF (RegSet.subset_erase_of hΦF (RegSet.subset_erase_of hΦF
      (RegSet.subset_erase_of hΦF (RegSet.subset_erase_of hΦF hΦ hra) h0) h1) h2) h3) h4) h5) h6

end RISCV64.Taint

namespace RISCV64

open VG.Taint in
/-- The analysis of `taint` is monotone, with the meet as frames. -/
instance : LeFrame taint where
  le_right {_ b} _ := RegSet.subset_refl b
  le_trans h₁ h₂ := RegSet.subset_trans h₁ h₂
  step i h hs := by
    obtain ⟨σ', h₁, h₂⟩ := Taint.step_mono i h ((taint_step _ i).symm.trans hs)
    exact ⟨σ', (taint_step _ i).trans h₁, h₂⟩
  condPub c h hc := Taint.condPub_mono c h hc
  meet h₁ h₂ := RegSet.inter_mono h₁ h₂
  call h hs := by cases hs; exact ⟨_, rfl, Taint.callErase_mono h⟩
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
  step_keeps i hk hΦF hΦ hs := Taint.step_keeps i hk hΦF hΦ ((taint_step _ i).symm.trans hs)
  call_keeps hk hΦF hΦ hs := by cases hs; exact Taint.callErase_keeps hk hΦF hΦ
  ret_keeps _ _ hΦ hs := by cases hs; exact hΦ
  push_keeps i _ _ hΦ hs := Taint.push_keeps i hΦ hs
  pop_keeps i hk hΦF hΦ hs := Taint.pop_keeps i hk hΦF hΦ hs

open VG.Taint in
/-- The analysis of `taintSym L` is `taint`'s, but for the addresses of the
statics of `L`, which it makes public: monotone, with the meet as frames. -/
instance (L : List String) : LeFrame (taintSym L) where
  le_right {_ b} _ := RegSet.subset_refl b
  le_trans h₁ h₂ := RegSet.subset_trans h₁ h₂
  step i h hs := by
    obtain ⟨σ', h₁, h₂⟩ := Taint.step_mono (i.symLi L) h ((taintSym_step L _ i).symm.trans hs)
    exact ⟨σ', (taintSym_step L _ i).trans h₁, h₂⟩
  condPub c h hc := Taint.condPub_mono c h hc
  meet h₁ h₂ := RegSet.inter_mono h₁ h₂
  call h hs := by cases hs; exact ⟨_, rfl, Taint.callErase_mono h⟩
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
  step_keeps i hk hΦF hΦ hs :=
    Taint.step_keeps (i.symLi L) ((Taint.keepsI_symLi L _ i).trans hk) hΦF hΦ
      ((taintSym_step L _ i).symm.trans hs)
  call_keeps hk hΦF hΦ hs := by cases hs; exact Taint.callErase_keeps hk hΦF hΦ
  ret_keeps _ _ hΦ hs := by cases hs; exact hΦ
  push_keeps i _ _ hΦ hs := Taint.push_keeps i hΦ hs
  pop_keeps i hk hΦF hΦ hs := Taint.pop_keeps i hk hΦF hΦ hs

end RISCV64

/-- Equality of RISC-V code, for summaries of code that is not a call. -/
instance : VG.Taint.CodeEq RISCV64.isa := ⟨@VG.Taint.codeBeq RISCV64.Instr RISCV64.Cond _ _⟩

end VG
