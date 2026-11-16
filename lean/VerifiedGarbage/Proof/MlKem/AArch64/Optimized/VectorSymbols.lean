module

public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Vector taint tracking with public addresses of read-only tables

This proof-only analysis extends the existing vector analysis exactly at
`adrSym`; the public contract must relate every named symbol address.
-/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized.VectorSymbols
open VG VG.AArch64
open VG.AArch64.VectorTaint

def Agree (names : List String) (τ : T) (s u : State) : Prop :=
  VectorTaint.Agree τ s u ∧ ∀name∈names,s.syms name=u.syms name

def step (names : List String) (τ : T) (i : Instr) : Option T :=
  match i.sym with
  | some (d,name) => if name∈names then some (Taint.set τ.1 d true,τ.2) else VectorTaint.step τ i
  | none => VectorTaint.step τ i

theorem step_sound {names : List String} {τ τ' : T} {i : Instr} {s u s' u' : State}
    (h : Agree names τ s u) (hs : step names τ i=some τ')
    (es : exec i s=some s') (eu : exec i u=some u') :
    addrs i s=addrs i u ∧ Agree names τ' s' u' := by
  have hy : ∀name∈names,s'.syms name=u'.syms name := by
    intro name hn; rw [exec_syms es,exec_syms eu]; exact h.2 name hn
  unfold step at hs
  split at hs
  · rename_i d name hi
    obtain rfl := Instr.sym_eq hi
    split at hs
    · rename_i hn
      cases hs
      simp only [exec,Option.some.injEq] at es eu
      subst es; subst eu
      exact ⟨rfl,⟨h.1.1.write .x d (p:=true) (fun _=>h.2 name hn),h.1.2⟩,hy⟩
    · have ht := VectorTaint.step_sound h.1 hs es eu
      exact ⟨ht.1,ht.2,hy⟩
  · have ht := VectorTaint.step_sound h.1 hs es eu
    exact ⟨ht.1,ht.2,hy⟩

/-! The step the kernel evaluates: `step` is built on `VectorTaint.step`, which
gives a taint whose sets are terms in the sets before, so no two taints of a
check are the same term, and the kernel analyses again code that repeats from
the same taint. `stepK` is `step` (`stepK_eq`), built on the vector analysis's
evaluated step (`VectorTaint.stepFn`): it matches on the instruction once with
its cases closed (`inline_match%`) and gives a taint whose set the instruction
writes is evaluated (`RegSet.force`). -/

/-- `step`, as a function of the instruction first. -/
def stepFn : Instr → List String → VectorTaint.Step
  | .adrSym d name => fun names => ⟨fun g v => (Taint.set g d (decide (name ∈ names))).force fun g' =>
      some (@Prod.mk (RegSet Reg) (RegSet VReg) g' v)⟩
  | i => fun _ => VectorTaint.stepFn i

/-- `stepFn`, with its cases closed (`inline_match%`). -/
def stepFnK : Instr → List String → VectorTaint.Step :=
  inline_match% stepFn VectorTaint.stepFn Taint.stepFn VectorTaint.scalar VectorTaint.ordinary

theorem stepFnK_eq (i : Instr) : stepFnK i = stepFn i := by cases i <;> rfl

/-- `step`, giving a taint that is evaluated. -/
def stepK (names : List String) (τ : T) (i : Instr) : Option T :=
  match τ with
  | (g, v) => (stepFnK i names).run g v

theorem vectorStepFn_run (g : RegSet Reg) (v : RegSet VReg) (i : Instr) :
    (VectorTaint.stepFn i).run g v = VectorTaint.step (g, v) i := by
  rw [← VectorTaint.stepFnK_eq]; exact congrFun (congrFun VectorTaint.stepK_eq (g, v)) i

theorem stepFn_of_sym_none {i : Instr} (h : i.sym = none) (names : List String) :
    stepFn i names = VectorTaint.stepFn i := by
  cases i <;> first | rfl | cases h

theorem stepK_eq (names : List String) : stepK names = step names := by
  funext ⟨g, v⟩ i
  show (stepFnK i names).run g v = step names (g, v) i
  rw [stepFnK_eq]
  cases hi : i.sym with
  | none =>
    rw [stepFn_of_sym_none hi, vectorStepFn_run]
    simp only [step, hi]
  | some p =>
    obtain ⟨d, name⟩ := p
    obtain rfl := Instr.sym_eq hi
    show some (Taint.set g d (decide (name ∈ names)), v) =
      if name ∈ names then some (Taint.set g d true, v) else VectorTaint.step (g, v) (.adrSym d name)
    by_cases hn : name ∈ names
    · rw [ite_eq_left hn, decide_eq_true hn]
    · rw [ite_eq_right hn, decide_eq_false hn]; rfl

def analysis (names : List String) : VG.Taint isa where
  T := T
  Agree := Agree names
  step := stepK names
  step_sound h hs := step_sound h ((congrFun (congrFun (stepK_eq names) _) _).symm.trans hs)
  condPub := VectorTaint.taint.condPub
  cond_sound h := VectorTaint.taint.cond_sound h.1
  meet := VectorTaint.taint.meet
  meet_left h := ⟨VectorTaint.taint.meet_left h.1,h.2⟩
  meet_right h := ⟨VectorTaint.taint.meet_right h.1,h.2⟩
  le := VectorTaint.taint.le
  le_sound hl h := ⟨VectorTaint.taint.le_sound hl h.1,h.2⟩
  call := VectorTaint.taint.call
  call_sound h hs es eu := by
    have ht := VectorTaint.taint.call_sound h.1 hs es eu
    simp only [isa,call,Option.some.injEq] at es eu
    subst es; subst eu
    exact ⟨ht.1,ht.2,h.2⟩
  ret := VectorTaint.taint.ret
  ret_sound h hs es eu := by
    have ht := VectorTaint.taint.ret_sound h.1 hs es eu
    simp only [isa,ret] at es eu
    split at es <;> [skip; cases es]
    split at eu <;> [skip; cases eu]
    cases es; cases eu
    exact ⟨ht.1,ht.2,h.2⟩
  push := VectorTaint.taint.push
  push_sound h hs es eu := by
    have ht := VectorTaint.taint.push_sound h.1 hs es eu
    exact ⟨ht.1,ht.2,fun name hn=>by rw [push_syms es,push_syms eu]; exact h.2 name hn⟩
  pop := VectorTaint.taint.pop
  pop_sound h hs es eu := by
    have ht := VectorTaint.taint.pop_sound h.1 hs es eu
    exact ⟨ht.1,ht.2,fun name hn=>by rw [pop_syms es,pop_syms eu]; exact h.2 name hn⟩

/-- The step of `analysis` is `step`, for the proofs about it: the kernel
evaluates `stepK`. -/
theorem analysis_step (names : List String) (τ : T) (i : Instr) :
    (analysis names).step τ i = step names τ i :=
  congrFun (congrFun (stepK_eq names) τ) i

end VG.Proof.MlKem.AArch64.Optimized.VectorSymbols
