module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# AArch64: code that never touches PSTATE.DIT runs the same from either DIT

Only `mrsDit` reads PSTATE.DIT and only `msrDitImm` writes it
(`TCB/AArch64/Isa.lean`), so code with neither runs, with the same trace,
from a state with the other DIT, and ends in its end state with that DIT
(`Exec.withDit`). A callee with neither is then constant time from public
data that agree but in DIT (`ConstantTime.withDit`).
-/

@[expose] public section

namespace VG.AArch64

/-- `mrsDit` and `msrDitImm`, the instructions that read or write PSTATE.DIT. -/
def Instr.touchesDit : Instr → Bool
  | .mrsDit _ | .msrDitImm _ => true
  | _ => false

/-- `s` with PSTATE.DIT `d`. -/
abbrev State.withDit (s : State) (d : Bool) : State := { s with dit := d }

theorem withDit_ite {c : Prop} [Decidable c] (a b : State) (d : Bool) :
    (if c then a else b).withDit d = if c then a.withDit d else b.withDit d := by
  split <;> rfl

theorem stackArg_withDit (s : State) (d : Bool) (i : Nat) : stackArg (s.withDit d) i = stackArg s i := rfl

theorem eval_withDit (c : Cond) (s : State) (d : Bool) : eval c (s.withDit d) = eval c s := by
  cases c <;> rfl

theorem store_withDit (s : State) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (d : Bool) :
    (s.withDit d).store a n v = (s.store a n v).map (State.withDit · d) := by
  unfold State.store; split <;> rfl

theorem exec_withDit {i : Instr} (hi : i.touchesDit = false) (s : State) (d : Bool) :
    exec i (s.withDit d) = (exec i s).map (State.withDit · d) := by
  cases i <;> simp only [Instr.touchesDit, Bool.true_eq_false] at hi
  all_goals first
    | rfl
    | (simp only [reduceExec, Option.map_map, Function.comp_def]; rfl)
    | (simp only [reduceExec, State.store, apply_ite (Option.map _), Option.map_some, Option.map_none,
        Option.map_map, Option.map_bind, Function.comp_def, withDit_ite]; rfl)
    | skip
  case stp =>
    simp only [reduceExec, store_withDit, Option.bind_map, apply_ite (Option.map _), Option.map_none,
      Option.map_bind, Function.comp_def]
    rfl

theorem addrs_withDit (i : Instr) (s : State) (d : Bool) : addrs i (s.withDit d) = addrs i s := by
  cases i <;> rfl

theorem push_withDit (i : Instr) (s : State) (d : Bool) :
    push i (s.withDit d) = (push i s).map (State.withDit · d) := by
  cases i <;> simp only [push, Option.map_none] <;>
    simp only [apply_ite (Option.map _), Option.map_some, Option.map_none] <;> rfl

theorem pop_withDit (i : Instr) (s₁ s₂ : State) (d₁ d₂ : Bool) :
    pop i (s₁.withDit d₁) (s₂.withDit d₂) = (pop i s₁ s₂).map (State.withDit · d₂) := by
  cases i <;> simp only [pop, Option.map_none] <;>
    simp only [apply_ite (Option.map _), Option.map_some, Option.map_none] <;> rfl

theorem ret_withDit (s₁ s₂ : State) (d₁ d₂ : Bool) :
    ret (s₁.withDit d₁) (s₂.withDit d₂) = (ret s₁ s₂).map (State.withDit · d₂) := by
  simp only [ret, apply_ite (Option.map _), Option.map_some, Option.map_none]

theorem call_withDit (s : State) (d : Bool) : call (s.withDit d) = (call s).map (State.withDit · d) := rfl

theorem execBlock_withDit {is : List Instr} (hc : ∀ i ∈ is, i.touchesDit = false) {s s' : State}
    {t : List Leak} (h : execBlock isa is s = some (s', t)) (d : Bool) :
    execBlock isa is (s.withDit d) = some (s'.withDit d, t) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h ⊢
    rw [h.1, h.2]; exact ⟨rfl, rfl⟩
  | cons i is ih =>
    have hi := hc i (List.mem_cons_self ..)
    have ex := exec_withDit hi s d
    have ad := addrs_withDit i s d
    simp only [execBlock] at h ⊢
    cases he : exec i s with
    | none => rw [he] at h; cases h
    | some s₁ =>
      rw [he] at ex
      rw [he] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨u, t'⟩, h₂, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [ex, Option.map_some, ad, ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h₂]

/-- Code that never reads or writes PSTATE.DIT runs, with the same trace, from either DIT. -/
theorem Exec.withDit {c : Prog isa} (hc : c.all (fun i => !i.touchesDit) = true)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') (d : Bool) :
    Exec isa c (s.withDit d) t (s'.withDit d) := by
  induction h with
  | block h =>
    simp only [Code.all, List.all_eq_true, Bool.not_eq_true'] at hc
    exact .block (execBlock_withDit hc h d)
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.all, Bool.and_eq_true] at hc
    exact .seq (ih₁ hc.1) (ih₂ hc.2)
  | iteT he _ ih =>
    simp only [Code.all, Bool.and_eq_true] at hc
    exact .iteT (by rw [show isa.eval _ _ = eval _ _ from rfl, eval_withDit]; exact he) (ih hc.1)
  | iteF he _ ih =>
    simp only [Code.all, Bool.and_eq_true] at hc
    exact .iteF (by rw [show isa.eval _ _ = eval _ _ from rfl, eval_withDit]; exact he) (ih hc.2)
  | loopExit _ he ih =>
    exact .loopExit (ih hc) (by rw [show isa.eval _ _ = eval _ _ from rfl, eval_withDit]; exact he)
  | loopNext _ he _ ih₁ ih₂ =>
    exact .loopNext (ih₁ hc) (by rw [show isa.eval _ _ = eval _ _ from rfl, eval_withDit]; exact he) (ih₂ hc)
  | @frame i j body s s₁ s₂ s' t hp _ hq ih =>
    simp only [Code.all, Bool.and_eq_true] at hc
    have e := Exec.frame (M := isa) (i := i) (j := j)
      (show isa.push i (s.withDit d) = some (s₁.withDit d) by
        rw [show isa.push i _ = push i _ from rfl, push_withDit]
        rw [show isa.push i s = push i s from rfl] at hp; rw [hp]; rfl)
      (ih hc.1.2)
      (show isa.pop j (s₁.withDit d) (s₂.withDit d) = some (s'.withDit d) by
        rw [show isa.pop j _ _ = pop j _ _ from rfl, pop_withDit]
        rw [show isa.pop j s₁ s₂ = pop j s₁ s₂ from rfl] at hq; rw [hq]; rfl)
    rwa [show isa.addrs i (s.withDit d) = isa.addrs i s from addrs_withDit i s d,
      show isa.addrs j (s₂.withDit d) = isa.addrs j s₂ from addrs_withDit j s₂ d] at e
  | @call n body s s₁ s₂ s' t hc₁ _ hr ih =>
    have hc₁' : isa.call (s.withDit d) = some (s₁.withDit d) := by
      rw [show isa.call _ = call _ from rfl, call_withDit]
      rw [show isa.call s = call s from rfl] at hc₁; rw [hc₁]; rfl
    have hr' : isa.ret (s₁.withDit d) (s₂.withDit d) = some (s'.withDit d) := by
      rw [show isa.ret _ _ = ret _ _ from rfl, ret_withDit]
      rw [show isa.ret s₁ s₂ = ret s₁ s₂ from rfl] at hr; rw [hr]; rfl
    exact Exec.call (name := n) (s₂ := s₂.withDit d) hc₁' (ih hc) hr'
  | @icall i n body next s s₁ s₂ s' t hi hc₁ _ hr ih =>
    simp only [Code.all, Bool.and_eq_true] at hc
    have hc₁' : isa.call (s.withDit d) = some (s₁.withDit d) := by
      rw [show isa.call _ = call _ from rfl, call_withDit]
      rw [show isa.call s = call s from rfl] at hc₁; rw [hc₁]; rfl
    have hr' : isa.ret (s₁.withDit d) (s₂.withDit d) = some (s'.withDit d) := by
      rw [show isa.ret _ _ = ret _ _ from rfl, ret_withDit]
      rw [show isa.ret s₁ s₂ = ret s₁ s₂ from rfl] at hr; rw [hr]; rfl
    have hi' : isa.icall i (s.withDit d) = some (isa.fnAddr (s.withDit d) n) := by
      cases i <;> exact hi
    have e := Exec.icall (next := next) (s₂ := s₂.withDit d) hi' hc₁' (ih hc.1.2) hr'
    rwa [show isa.addrs i (s.withDit d) = isa.addrs i s from addrs_withDit i s d] at e
  | @icallNext i n body n' body' next s s' t a ha hne _ ih =>
    have ha' : isa.icall i (s.withDit d) = some a := by cases i <;> exact ha
    exact Exec.icallNext ha' hne (ih (by simp only [Code.all, Bool.and_eq_true] at hc ⊢; exact hc.2))

/-- A callee that never touches PSTATE.DIT is constant time from public data
that agree but in DIT: its second run, from the first's DIT instead, leaks the
same (`Exec.withDit`). So a caller proves its contract's public data of the
second run's entry with the first's DIT, which agrees by construction. -/
theorem ConstantTime.withDit {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop}
    (hc : c.all (fun i => !i.touchesDit) = true) (hct : ConstantTime isa pre pub c)
    (hpre : ∀ s d, pre s → pre (s.withDit d)) :
    ConstantTime isa pre (fun a b => pub a (b.withDit a.dit)) c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  exact hct s₁ (s₂.withDit s₁.dit) t₁ t₂ s₁' (s₂'.withDit s₁.dit) h₁ (hpre _ _ h₂) hp e₁
    (Exec.withDit hc e₂ _)

/-- `k`, its public data those of the second run's entry with the first's mode:
what a caller shows of a callee that never touches the mode (`Contract.ct_ditFree`). -/
def _root_.VG.Contract.ditFree (k : Contract isa) : Contract isa :=
  { k with pub := fun a b => k.pub a (b.withDit a.dit) }

theorem _root_.VG.Contract.ct_ditFree {k : Contract isa} {c : Prog isa} (hc : c.all (fun i => !i.touchesDit) = true)
    (hct : ConstantTime isa k.pre k.pub c) (hpre : ∀ s d, k.pre s → k.pre (s.withDit d)) :
    ConstantTime isa k.ditFree.pre k.ditFree.pub c :=
  ConstantTime.withDit hc hct hpre

/-- Constant time against public data with the mode, for code that never
touches it, is constant time against public data without it. -/
theorem ConstantTime.dropDit {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop}
    (hc : c.all (fun i => !i.touchesDit) = true) (hct : ConstantTime isa pre (fun a b => pub a b ∧ a.dit = b.dit) c)
    (hpre : ∀ s d, pre s → pre (s.withDit d)) (hpub : ∀ a b, pub a b → pub a (b.withDit a.dit)) :
    ConstantTime isa pre pub c := fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
  ConstantTime.withDit hc hct hpre s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨hpub _ _ hp, rfl⟩ e₁ e₂

end VG.AArch64
