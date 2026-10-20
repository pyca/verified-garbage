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

def analysis (names : List String) : VG.Taint isa where
  T := T
  Agree := Agree names
  step := step names
  step_sound := step_sound
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

end VG.Proof.MlKem.AArch64.Optimized.VectorSymbols
