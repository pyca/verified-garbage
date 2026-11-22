module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Framework.CallFill
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Impl.ICall

/-!
# Taint tracking through indirect calls of one function (ARMv7)

The analysis (`Taint.check`) fails on an indirect call. An indirect call of
one function, `Code.icalls i [(n, b)]` (`ldr r12, …; blx r12`), runs as the call of
`b`, observing the address it calls, `n`'s (`Exec.icall`): where two runs
agree on that address, the call is constant time as the call is. So such code
is checked with each of those indirect calls made a call (`Code.eraseI`), and
the check holds of the code itself for runs that agree on the addresses of the
functions it calls indirectly (`check_eraseI_sound`), which a contract makes
public (`Abi.withFns`). `eraseI` does not look into the bodies of calls, which
the check of a call analyses as they are.
-/

@[expose] public section

namespace VG.Arm

/-- `c` with each indirect call of one function made a call of it. -/
def Code.eraseI : Prog isa → Prog isa
  | .block is => .block is
  | .seq a b => .seq (eraseI a) (eraseI b)
  | .ite cd t e => .ite cd (eraseI t) (eraseI e)
  | .loop b cd => .loop (eraseI b) cd
  | .call n b => .call n b
  | .frame p b q => .frame p (eraseI b) q
  | .icall i n b nx => match nx with
    | .block [] => .call n b
    | nx => .icall i n b nx

/-- Every function `c` calls by an indirect call `eraseI` erases satisfies `P`. -/
def Code.IcallsP (P : String → Prop) : Prog isa → Prop
  | .block _ => True
  | .seq a b => IcallsP P a ∧ IcallsP P b
  | .ite _ t e => IcallsP P t ∧ IcallsP P e
  | .loop b _ => IcallsP P b
  | .call _ _ => True
  | .frame _ b _ => IcallsP P b
  | .icall _ n _ _ => P n

/-- Every indirect call of `c` that `IcallsP` looks at is of a hole (its body
`.block []`): with the holes filled (`Code.fillHoles`), of the function filled
in. -/
def Code.icallHoles : Prog isa → Bool
  | .block _ => true
  | .seq a b => icallHoles a && icallHoles b
  | .ite _ t e => icallHoles t && icallHoles e
  | .loop b _ => icallHoles b
  | .call _ _ => true
  | .frame _ b _ => icallHoles b
  | .icall _ _ b _ => match b with
    | .block [] => true
    | _ => false

theorem Code.icallsP_fillHoles {n : String} {b : Prog isa} :
    ∀ {e : Prog isa}, Code.icallHoles e = true → Code.IcallsP (· = n) (Code.fillHoles n b e)
  | .block _, _ => trivial
  | .seq x y, h => by
    simp only [Code.icallHoles, Bool.and_eq_true] at h
    exact ⟨icallsP_fillHoles h.1, icallsP_fillHoles h.2⟩
  | .ite _ t e, h => by
    simp only [Code.icallHoles, Bool.and_eq_true] at h
    exact ⟨icallsP_fillHoles h.1, icallsP_fillHoles h.2⟩
  | .loop x _, h => icallsP_fillHoles (e := x) h
  | .call m body, _ => by
    cases body with
    | block is => cases is <;> trivial
    | _ => trivial
  | .frame _ x _, h => icallsP_fillHoles (e := x) h
  | .icall _ _ x _, h => by
    cases x with
    | block is =>
      cases is with
      | nil => rfl
      | cons _ _ => simp [Code.icallHoles] at h
    | _ => simp [Code.icallHoles] at h

theorem icall_blx {i : Instr} {s : State} {a : Addr} (h : Arm.icall i s = some a) :
    ∃ r, i = .blx r := by
  cases i <;> simp [Arm.icall] at h
  exact ⟨_, rfl⟩

namespace Taint

variable {A : VG.Taint isa}

theorem check_eraseI_sound {P : String → Prop} {c : Prog isa} {τ τ' : A.T} {hc : VG.Taint.Hint A.T}
    {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak} (h : A.check τ (Code.eraseI c) hc = some τ')
    (ha : A.Agree τ s₁ s₂) (hy : ∀ n, P n → s₁.syms n = s₂.syms n) (hp : Code.IcallsP P c)
    (e₁ : Exec isa c s₁ t₁ s₁') (e₂ : Exec isa c s₂ t₂ s₂') : t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction e₁ generalizing τ τ' hc s₂ t₂ s₂' with
  | block h₁ => exact VG.Taint.check_sound h ha (.block h₁) e₂
  | @seq c₁ c₂ _ _ _ _ _ a₁ b₁ ih₁ ih₂ =>
    cases hc with
    | seq mid g₁ g₂ =>
      have h : ((A.check τ (Code.eraseI c₁) g₁).bind fun τ' =>
        if A.le mid τ' then A.check mid (Code.eraseI c₂) g₂ else none) = some τ' := h
      cases e₂ with
      | seq a b =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨τ₁, h₁, h₂⟩ := h
        split at h₂ <;> [rename_i hle; cases h₂]
        obtain ⟨rfl, ha₁⟩ := ih₁ h₁ ha hy hp.1 a
        obtain ⟨rfl, ha₂⟩ := ih₂ h₂ (A.le_sound hle ha₁)
          (fun n hn => by rw [Exec.syms a₁, Exec.syms a]; exact hy n hn) hp.2 b
        exact ⟨rfl, ha₂⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @iteT cnd t e _ _ _ hc' _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ (Code.eraseI t) g₁).bind fun τ₁ =>
            (A.check τ (Code.eraseI e) g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hq; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, _, rfl⟩ := h
      cases e₂ with
      | iteT _ b => obtain ⟨rfl, hq'⟩ := ih h₁ ha hy hp.1 b; exact ⟨rfl, A.meet_left hq'⟩
      | iteF hc'' _ => rw [← A.cond_sound ha hq, hc'] at hc''; cases hc''
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @iteF cnd t e _ _ _ hc' _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ (Code.eraseI t) g₁).bind fun τ₁ =>
            (A.check τ (Code.eraseI e) g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hq; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, _, τ₂, h₂, rfl⟩ := h
      cases e₂ with
      | iteT hc'' _ => rw [← A.cond_sound ha hq, hc'] at hc''; cases hc''
      | iteF _ b => obtain ⟨rfl, hq'⟩ := ih h₂ ha hy hp.2 b; exact ⟨rfl, A.meet_right hq'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopExit body c _ _ _ _ hc' ih =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ (Code.eraseI body) hb).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopExit a _ => obtain ⟨rfl, hq⟩ := ih hb' hσ hy hp a; exact ⟨rfl, hq⟩
      | loopNext a hc'' _ =>
        obtain ⟨_, ha₁⟩ := ih hb' hσ hy hp a
        rw [← A.cond_sound ha₁ hl.2, hc'] at hc''; cases hc''
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopNext body c _ _ _ _ _ a₁ hc' _ ih₁ ih₂ =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ (Code.eraseI body) hb).bind fun σ' =>
            if A.le σ σ' && A.condPub σ' c then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopExit a hc'' =>
        obtain ⟨_, ha₁⟩ := ih₁ hb' hσ hy hp a
        rw [← A.cond_sound ha₁ hl.2, hc'] at hc''; cases hc''
      | loopNext a _ b =>
        obtain ⟨rfl, ha₁⟩ := ih₁ hb' hσ hy hp a
        have hloop : A.check τ' (Code.eraseI (.loop body c)) (.loop σ hb) = some τ' := by
          show (if A.le σ τ' then
            (A.check σ (Code.eraseI body) hb).bind fun σ' =>
              if A.le σ σ' && A.condPub σ' c then some σ' else none
            else none) = some τ'
          simp only [hl.1, hl.2, hb', Option.bind_some, Bool.and_self, ite_true]
        obtain ⟨rfl, ha₂⟩ := ih₂ hloop ha₁
          (fun n hn => by rw [Exec.syms a₁, Exec.syms a]; exact hy n hn) hp b
        exact ⟨rfl, ha₂⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | call hc₁ hb hr => exact VG.Taint.check_sound h ha (.call hc₁ hb hr) e₂
  | @frame i j body _ _ _ _ _ hp₁ _ hq ih =>
    cases hc with
    | frame hb =>
      have h : ((A.push τ i).bind fun τ₁ =>
        (A.check τ₁ (Code.eraseI body) hb).bind fun τ₂ => A.pop τ₂ j) = some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₂ with
      | frame hp₂ b hq₂ =>
        obtain ⟨ha₁, ha₁'⟩ := A.push_sound ha h₁ hp₁ hp₂
        obtain ⟨rfl, ha₂⟩ := ih h₂ ha₁'
          (fun n hn => by rw [push_syms hp₁, push_syms hp₂]; exact hy n hn) hp b
        obtain ⟨ha₃, ha₃'⟩ := A.pop_sound ha₂ h₃ hq hq₂
        exact ⟨by rw [ha₁, ha₃], ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @icall i name body next _ _ _ _ _ hi hc₁ hb hr _ =>
    cases next with
    | block is =>
      cases is with
      | nil =>
        have hcall : A.check τ (.call name body) hc = some τ' := h
        cases e₂ with
        | icall hi₂ hc₂ hb₂ hr₂ =>
          obtain ⟨ht, hag⟩ := VG.Taint.check_sound hcall ha (.call hc₁ hb hr) (.call hc₂ hb₂ hr₂)
          obtain ⟨r, rfl⟩ := icall_blx hi
          refine ⟨?_, hag⟩
          simp only [addrs, List.map_nil, List.nil_append, List.cons.injEq] at ht ⊢
          exact ⟨congrArg (fun x : BitVec 32 => Leak.addr (x.setWidth 64)) (hy name hp), ht⟩
      | cons _ _ =>
        have h' : (none : Option A.T) = some τ' := by cases hc <;> exact h
        cases h'
    | _ =>
      have h' : (none : Option A.T) = some τ' := by cases hc <;> exact h
      cases h'
  | icallNext =>
    have h' : (none : Option A.T) = some τ' := by cases hc <;> exact h
    cases h'

end Taint

end VG.Arm

namespace VG.Arm

/-- An indirect call of one function by `blx r`, where `r` holds its
address, runs as its call. -/
theorem WP.icall1 {r : Reg} {n : String} {c : Prog isa} {s : State} {Q : State → Prop}
    (hr : s.gpr r = s.syms n) (h : WP isa (.call n c) s Q) : WP isa (Code.icalls (.blx r) [(n, c)]) s Q :=
  WP.icalls_of_call (M := isa) (a := (s.syms n).setWidth 64)
    (by show some ((s.gpr r).setWidth 64) = _; rw [hr])
    (by
      show List.find? (fun p => isa.fnAddr s p.1 == (s.syms n).setWidth 64) [(n, c)] = some (n, c)
      exact List.find?_cons_of_pos (beq_self_eq_true _)) h

end VG.Arm
