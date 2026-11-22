module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved

/-!
# `CodeOk` of code generic over a function it calls (ARMv7)

A function generic over an implementation it calls has code that is not a
closed term. `FillB a b` says that `b` is the code `a` with some of its holes
(`holeStub k`, a frame of `k` bytes around nothing) replaced by code that
meets `CodeOk _ k`, and its calls' names changed: `a` is the function's code
with a stub, whose `CodeOk` the kernel evaluates once (`lit_decide`), and `b`
its code with an implementation, which `fill_holes` walks, never the
implementation's code. `FillB.codeOk` joins the two.
-/

@[expose] public section

namespace VG.Arm.ScrubFill

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-- A stub's place for an implementation that uses at most `k` bytes of
stack: a frame of `k` bytes around nothing. -/
def holeStub (k : Nat) : Prog isa := .frame (.alloc k) (.block []) (.free k)

/-- `b` is `a` with some of its holes (`holeStub k`) replaced by code that
meets `CodeOk _ k`, and the names of its calls changed. -/
inductive FillB : Prog isa → Prog isa → Prop
  | refl (a : Prog isa) : FillB a a
  | hole {k : Nat} {d : Prog isa} : CodeOk d k → FillB (holeStub k) d
  | seq {a b a' b' : Prog isa} : FillB a a' → FillB b b' → FillB (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : FillB t t' → FillB e e' → FillB (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : FillB b b' → FillB (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : FillB b b' → FillB (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : FillB b b' → FillB (.frame i b j) (.frame i b' j)

theorem FillB.codeOk {a b : Prog isa} (h : FillB a b) : ∀ {n : Nat}, CodeOk a n → CodeOk b n := by
  induction h with
  | refl => exact id
  | hole hd =>
    intro n ha
    exact hd.mono (by simpa only [holeStub, armStack, Nat.zero_add] using ha.1)
  | seq _ _ iha ihb =>
    intro n ha
    simp only [CodeOk, armStack, noIcall, Nat.max_le, Bool.and_eq_true] at ha
    exact CodeOk.seq (iha ⟨ha.1.1, ha.2.1⟩) (ihb ⟨ha.1.2, ha.2.2⟩)
  | ite _ _ _ iht ihe =>
    intro n ha
    simp only [CodeOk, armStack, noIcall, Nat.max_le, Bool.and_eq_true] at ha
    exact CodeOk.ite (iht ⟨ha.1.1, ha.2.1⟩) (ihe ⟨ha.1.2, ha.2.2⟩)
  | loop _ _ ih =>
    intro n ha
    exact CodeOk.loop (ih ha)
  | call _ _ _ ih =>
    intro n ha
    exact CodeOk.call (ih ha)
  | frame i j _ ih =>
    intro n ha
    obtain ⟨hs, hi⟩ := ha
    cases i with
    | push rs =>
      simp only [armStack] at hs
      obtain ⟨hs', hi'⟩ := ih (n := n - 4 * rs.length) ⟨by omega, hi⟩
      exact ⟨by simp only [armStack]; omega, hi'⟩
    | alloc k =>
      simp only [armStack] at hs
      obtain ⟨hs', hi'⟩ := ih (n := n - k) ⟨by omega, hi⟩
      exact ⟨by simp only [armStack]; omega, hi'⟩
    | _ => exact ih ⟨hs, hi⟩

/-- Proves `FillB a b` of a function's code with stubs (`a`, its holes
`holeStub k`) and with an implementation (`b`), from hypotheses `CodeOk c k`
of the implementation's code `c`: code the two share is matched as one term
(`FillB.refl`, at reducible transparency, so it is not unfolded). -/
macro "fill_holes" : tactic => `(tactic| repeat' (first
  | with_reducible exact FillB.refl _
  | exact FillB.hole (by with_reducible assumption)
  | refine FillB.seq ?_ ?_
  | refine FillB.ite _ ?_ ?_
  | refine FillB.loop _ ?_
  | refine FillB.call _ _ ?_
  | refine FillB.frame _ _ ?_))

end VG.Arm.ScrubFill
