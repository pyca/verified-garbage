import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.RegSetOrder

/-!
# The AArch64 taint analyses are monotone

With more registers public on entry, every step of `AArch64.taint` and
`AArch64.VectorTaint.taint` succeeds, with more registers public after it
(`Taint.Mono`), so their checks can use summaries of called functions
(`taint_decide_sum`).
-/

namespace VG


namespace AArch64.Taint

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
    | (cases hs; exact ⟨_, rfl, h⟩)
    | (cases hs; refine ⟨_, rfl, set_mono h _ fun hp => ?_⟩
       simp only [Bool.and_eq_true] at hp ⊢
       exact ⟨⟨pub_mono h hp.1.1, pub_mono h hp.1.2⟩, pub_mono h hp.2⟩)
    | (split at hs <;> [rename_i hn; cases hs]
       cases hs
       exact ⟨_, by simp only [pub_mono h hn, ↓reduceIte]; rfl, (by first | exact set_mono h _ id | exact h)⟩)

theorem condPub_mono {τ σ : T} (c : Cond) (h : τ.subset σ = true)
    (hc : AArch64.taint.condPub τ c = true) : AArch64.taint.condPub σ c = true := by
  cases c <;> exact pub_mono h hc

theorem call_mono {τ σ τ' : T} (h : τ.subset σ = true) (hs : AArch64.taint.call τ = some τ') :
    ∃ σ', AArch64.taint.call σ = some σ' ∧ τ'.subset σ' = true := by
  cases hs
  exact ⟨_, rfl, RegSet.erase_mono (RegSet.erase_mono (RegSet.erase_mono h _) _) _⟩

theorem push_mono {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true) (hs : Taint.push τ i = some τ') :
    ∃ σ', Taint.push σ i = some σ' ∧ τ'.subset σ' = true := by
  cases i <;> simp only [push, reduceCtorEq] at hs ⊢ <;> cases hs <;> exact ⟨_, rfl, h⟩

theorem pop_mono {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true) (hs : Taint.pop τ i = some τ') :
    ∃ σ', Taint.pop σ i = some σ' ∧ τ'.subset σ' = true := by
  cases i <;> simp only [pop, reduceCtorEq] at hs ⊢ <;> cases hs
  · exact ⟨_, rfl, RegSet.erase_mono h _⟩
  · exact ⟨_, rfl, h⟩

/-- The general-purpose register an instruction writes, if any. -/
def gprDst : Instr → Option Reg
  | .add _ d .. | .sub _ d .. | .adds _ d .. | .subs _ d .. | .logic _ _ d .. | .logicRor _ _ d ..
  | .bicRor _ d .. | .extr _ d .. | .mul _ d .. | .umulh d .. | .adcs _ d .. | .sbcs _ d ..
  | .adc _ d .. | .sbc _ d .. | .csel _ d .. | .adrSym d _
  | .madd _ d .. | .addImm _ d .. | .subImm _ d .. | .ror _ d .. | .lsr _ d .. | .lsl _ d ..
  | .rev32 d _ | .rev d _ | .addSp d _ | .movz _ d .. | .movk _ d .. | .ldr _ d .. | .ldrb d ..
  | .ldrSp d _ | .umov _ d .. | .pop d => some d
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
    | (cases hs; exact hΦ)
    | (split at hs <;> [skip; cases hs]
       cases hs
       first | exact set_keeps hΦF hΦ hk _ | exact hΦ)

end AArch64.Taint

namespace AArch64.VectorTaint

theorem setV_mono {τ σ : RegSet VReg} (h : τ.subset σ = true) (d : VReg) {p q : Bool}
    (hpq : p = true → q = true) : (setV τ d p).subset (setV σ d q) = true := by
  unfold setV
  cases p <;> cases q <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · exact RegSet.erase_mono h d
  · exact RegSet.subset_trans (RegSet.erase_subset τ d)
      (RegSet.subset_trans h (RegSet.subset_insert σ d))
  · exact absurd (hpq rfl) Bool.false_ne_true
  · exact RegSet.insert_mono h d

theorem afterV_mono {τ σ : RegSet VReg} (h : τ.subset σ = true) (i : Instr) :
    (afterV τ i).subset (afterV σ i) = true := by
  unfold afterV
  split
  · exact h
  · exact RegSet.subset_refl _

theorem le_iff {τ σ : T} : taint.le τ σ = true ↔ τ.1.subset σ.1 = true ∧ τ.2.subset σ.2 = true := by
  show (τ.1.subset σ.1 && τ.2.subset σ.2) = true ↔ _
  rw [Bool.and_eq_true]

theorem step_mono {τ σ τ' : T} (i : Instr) (h : taint.le τ σ = true) (hs : step τ i = some τ') :
    ∃ σ', step σ i = some σ' ∧ taint.le τ' σ' = true := by
  rw [le_iff] at h
  have ordinary : (Taint.step τ.1 i).map (fun g => (g, afterV τ.2 i)) = some τ' →
      ∃ σ', (Taint.step σ.1 i).map (fun g => (g, afterV σ.2 i)) = some σ' ∧
        taint.le τ' σ' = true := fun hs => by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨g', hg', hle⟩ := Taint.step_mono i h.1 hg
    exact ⟨_, by rw [hg']; rfl, le_iff.mpr ⟨hle, afterV_mono h.2 i⟩⟩
  cases i with
  | vop op =>
    cases op <;> try exact ordinary hs
    case dup a d n =>
      simp only [step, Option.some.injEq] at hs; subst hs
      exact ⟨_, rfl, le_iff.mpr ⟨h.1, setV_mono h.2 d (Taint.pub_mono h.1)⟩⟩
  | umov sz d n k =>
    simp only [step, Option.some.injEq] at hs; subst hs
    exact ⟨_, rfl, le_iff.mpr ⟨Taint.set_mono h.1 d (RegSet.mem_mono h.2), h.2⟩⟩
  | _ => exact ordinary hs

theorem le_refl (τ : T) : taint.le τ τ = true := le_iff.mpr ⟨RegSet.subset_refl _, RegSet.subset_refl _⟩

/-- What of the vector registers `F` an instruction keeps public: a `dup` all
but its destination, a `umov` and a scalar instruction all of them, any other
instruction none. -/
def vkeeps (F : RegSet VReg) : Instr → Bool
  | .vop (.dup _ d _) => !F.mem d
  | .umov .. => true
  | i => scalar i

/-- An instruction keeps what is public of `F`, a set of general-purpose
registers it does not write, and of vector registers it does not write
(`vkeeps`). -/
def keeps (F : T) (i : Instr) : Bool := (F.2.bits == 0 || vkeeps F.2 i) && Taint.keepsI F.1 i

theorem keeps_vec {F : T} {i : Instr} (h : keeps F i = true) :
    F.2.bits = 0 ∨ vkeeps F.2 i = true := by
  simp only [keeps, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h; exact h.1

theorem keeps_gpr {F : T} {i : Instr} (h : keeps F i = true) : Taint.keepsI F.1 i = true := by
  simp only [keeps, Bool.and_eq_true] at h; exact h.2

theorem vec_sub {Φ F : T} (hΦF : taint.le Φ F = true) (h0 : F.2.bits = 0) (s : RegSet VReg) :
    Φ.2.subset s = true := by
  have h := (le_iff.mp hΦF).2
  refine RegSet.subset_iff.mpr fun i hi => ?_
  have := RegSet.subset_iff.mp h i hi
  rw [h0, Nat.zero_testBit] at this; cases this

theorem step_keeps {F Φ σ σ' : T} (i : Instr) (hk : keeps F i = true) (hΦF : taint.le Φ F = true)
    (hΦ : taint.le Φ σ = true) (hs : step σ i = some σ') : taint.le Φ σ' = true := by
  have hk' := keeps_vec hk
  have hg := keeps_gpr hk
  have hΦF' := (le_iff.mp hΦF).1
  have hΦ' := (le_iff.mp hΦ).1
  have hΦv := (le_iff.mp hΦ).2
  have ordinary : (Taint.step σ.1 i).map (fun g => (g, afterV σ.2 i)) = some σ' →
      Φ.2.subset (afterV σ.2 i) = true → taint.le Φ σ' = true := fun hs hv => by
    obtain ⟨g, hg', rfl⟩ := Option.map_eq_some_iff.mp hs
    exact le_iff.mpr ⟨Taint.step_keeps i hg hΦF' hΦ' hg', hv⟩
  -- An instruction that keeps no vector register: `F` has none.
  have none : vkeeps F.2 i = false → Φ.2.subset (afterV σ.2 i) = true := fun hn => by
    rcases hk' with h0 | hv
    · exact vec_sub hΦF h0 _
    · rw [hn] at hv; cases hv
  -- A scalar instruction keeps every vector register.
  have keepsAll : scalar i = true → Φ.2.subset (afterV σ.2 i) = true := fun hsc => by
    simp only [afterV, hsc, ↓reduceIte]; exact hΦv
  cases i with
  | vop op =>
    cases op
    case dup a d n =>
      simp only [step, Option.some.injEq] at hs; subst hs
      refine le_iff.mpr ⟨hΦ', ?_⟩
      rcases hk' with h0 | hv
      · exact vec_sub hΦF h0 _
      · simp only [vkeeps, Bool.not_eq_true'] at hv
        unfold setV; split
        · exact RegSet.subset_insert_of hΦv d
        · exact RegSet.subset_erase_of (le_iff.mp hΦF).2 hΦv hv
    all_goals exact ordinary hs (none rfl)
  | umov sz d n k =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [Taint.keepsI, Taint.gprDst, Bool.not_eq_true'] at hg
    exact le_iff.mpr ⟨Taint.set_keeps hΦF' hΦ' hg _, hΦv⟩
  | ldrq => exact ordinary hs (none rfl)
  | _ => exact ordinary hs (keepsAll rfl)

/-- A call writes `x16`, `x17` and `x30`. -/
def keepsCall (F : T) : Bool :=
  F.2.bits == 0 && !F.1.mem .x16 && !F.1.mem .x17 && !F.1.mem .x30

instance : VG.Taint.LeFrame taint where
  le_right {_ b} _ := le_refl b
  le_trans {_ _ _} h₁ h₂ :=
    le_iff.mpr ⟨RegSet.subset_trans (le_iff.mp h₁).1 (le_iff.mp h₂).1,
      RegSet.subset_trans (le_iff.mp h₁).2 (le_iff.mp h₂).2⟩
  step i h hs := step_mono i h hs
  condPub c h hc := Taint.condPub_mono c (le_iff.mp h).1 hc
  meet {_ _ _ _} h₁ h₂ :=
    le_iff.mpr ⟨RegSet.inter_mono (le_iff.mp h₁).1 (le_iff.mp h₂).1,
      RegSet.inter_mono (le_iff.mp h₁).2 (le_iff.mp h₂).2⟩
  call {τ σ τ'} h hs := by
    have hs : (AArch64.taint.call τ.1).map (fun g => (g, τ.2)) = some τ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨g', hg', hle⟩ := Taint.call_mono (le_iff.mp h).1 hg
    refine ⟨(g', σ.2), ?_, le_iff.mpr ⟨hle, (le_iff.mp h).2⟩⟩
    show (AArch64.taint.call σ.1).map (fun g => (g, σ.2)) = _
    rw [hg']; rfl
  ret h hs := by cases hs; exact ⟨_, rfl, h⟩
  push {τ σ τ'} i h hs := by
    have hs : (Taint.push τ.1 i).map (fun g => (g, τ.2)) = some τ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨g', hg', hle⟩ := Taint.push_mono i (le_iff.mp h).1 hg
    refine ⟨(g', σ.2), ?_, le_iff.mpr ⟨hle, (le_iff.mp h).2⟩⟩
    show (Taint.push σ.1 i).map (fun g => (g, σ.2)) = _
    rw [show Taint.push σ.1 i = some g' from hg']; rfl
  pop {τ σ τ'} i h hs := by
    have hs : (Taint.pop τ.1 i).map (fun g => (g, τ.2)) = some τ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨g', hg', hle⟩ := Taint.pop_mono i (le_iff.mp h).1 hg
    refine ⟨(g', σ.2), ?_, le_iff.mpr ⟨hle, (le_iff.mp h).2⟩⟩
    show (Taint.pop σ.1 i).map (fun g => (g, σ.2)) = _
    rw [show Taint.pop σ.1 i = some g' from hg']; rfl
  join a b := (a.1.union b.1, a.2.union b.2)
  bot := (RegSet.empty, RegSet.empty)
  join_lub {a b _} ha hb :=
    ⟨le_iff.mpr ⟨RegSet.subset_union_left _ _, RegSet.subset_union_left _ _⟩,
      le_iff.mpr ⟨RegSet.subset_union_right _ _, RegSet.subset_union_right _ _⟩,
      le_iff.mpr ⟨RegSet.union_subset (le_iff.mp ha).1 (le_iff.mp hb).1,
        RegSet.union_subset (le_iff.mp ha).2 (le_iff.mp hb).2⟩⟩
  frameOf := taint.meet
  frame_le_left _ _ := le_iff.mpr ⟨RegSet.inter_subset_left _ _, RegSet.inter_subset_left _ _⟩
  frame_le_right _ _ _ := le_iff.mpr ⟨RegSet.inter_subset_right _ _, RegSet.inter_subset_right _ _⟩
  frame_mono F h := le_iff.mpr ⟨RegSet.inter_mono (le_iff.mp h).1 (RegSet.subset_refl _),
    RegSet.inter_mono (le_iff.mp h).2 (RegSet.subset_refl _)⟩
  le_frame hb hc := le_iff.mpr ⟨RegSet.subset_inter (le_iff.mp hb).1 (le_iff.mp hc).1,
    RegSet.subset_inter (le_iff.mp hb).2 (le_iff.mp hc).2⟩
  le_meet hb hc := le_iff.mpr ⟨RegSet.subset_inter (le_iff.mp hb).1 (le_iff.mp hc).1,
    RegSet.subset_inter (le_iff.mp hb).2 (le_iff.mp hc).2⟩
  bot_le _ := le_iff.mpr ⟨RegSet.empty_subset _, RegSet.empty_subset _⟩
  bot_valid := le_refl _
  keeps := keeps
  keepsCall := keepsCall
  keeps_bot i := by
    have h : ∀ d : Reg, (RegSet.empty : RegSet Reg).mem d = false := fun d => by
      simp [RegSet.mem, RegSet.empty]
    simp only [keeps, Taint.keepsI]
    split
    · rw [h]; rfl
    · rfl
  keepsCall_bot := rfl
  step_keeps i hk hΦF hΦ hs := step_keeps i hk hΦF hΦ hs
  call_keeps {F Φ σ σ'} hk hΦF hΦ hs := by
    have hs : (AArch64.taint.call σ.1).map (fun g => (g, σ.2)) = some σ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    cases hg
    simp only [keepsCall, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hk
    have hΦF' := (le_iff.mp hΦF).1
    have hΦ' := (le_iff.mp hΦ).1
    refine le_iff.mpr ⟨?_, (le_iff.mp hΦ).2⟩
    exact RegSet.subset_erase_of hΦF' (RegSet.subset_erase_of hΦF'
      (RegSet.subset_erase_of hΦF' hΦ' hk.1.1.2) hk.1.2) hk.2
  ret_keeps _ _ hΦ hs := by cases hs; exact hΦ
  push_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : (Taint.push σ.1 i).map (fun g => (g, σ.2)) = some σ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    cases i <;> simp only [Taint.push, reduceCtorEq, Option.some.injEq] at hg <;> subst hg <;>
      exact hΦ
  pop_keeps {F Φ σ σ'} i hk hΦF hΦ hs := by
    have hs : (Taint.pop σ.1 i).map (fun g => (g, σ.2)) = some σ' := hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hg' := keeps_gpr hk
    cases i <;> simp only [Taint.pop, reduceCtorEq, Option.some.injEq] at hg <;> subst hg
    · simp only [Taint.keepsI, Taint.gprDst, Bool.not_eq_true'] at hg'
      exact le_iff.mpr ⟨RegSet.subset_erase_of (le_iff.mp hΦF).1 (le_iff.mp hΦ).1 hg',
        (le_iff.mp hΦ).2⟩
    · exact hΦ

end AArch64.VectorTaint

/-- Equality of AArch64 code, for summaries of code that is not a call. -/
instance : VG.Taint.CodeEq AArch64.isa := ⟨@VG.Taint.codeBeq AArch64.Instr AArch64.Cond _ _⟩

end VG
