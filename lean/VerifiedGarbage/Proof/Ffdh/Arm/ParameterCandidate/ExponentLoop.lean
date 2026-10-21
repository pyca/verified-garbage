module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentStep
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! The bounded native loop divides by precisely 2^sigma. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)

structure ExponentInv (s0 : State) (base : BitVec 32) (capacity w input sigma i left : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * capacity)
  ready : KeyReady base capacity w s
  data : MontData base capacity w s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩
  number : num s.mem (base + 96#32) (2 * w + 2) 27 = input / 2 ^ i
  saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = BitVec.ofNat 32 left
  remaining : i + left = sigma
  positive : 0 < left
  bound : left ≤ 4
  arrays : ∀ j, j < 30 → j ≠ 27 → num s.mem (base + 96#32) (2 * w + 2) j =
    num s0.mem (base + 96#32) (2 * w + 2) j
  header : ∀ d, d + 8 ≤ 256 → s.mem.readW (off (State.addr base) d) 64 =
    s0.mem.readW (off (State.addr base) d) 64
  frame : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s0.sp + 64#32), 4⟩] s0.mem s.mem
  rest : Rest opRegs s0 s

theorem exponentHalfLoop_ok {s : State} {base : BitVec 32} {capacity w input sigma : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (number : num s.mem (base + 96#32) (2 * w + 2) 27 = input)
    (positive : 0 < sigma) (bound : sigma ≤ 4)
    (saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = BitVec.ofNat 32 sigma) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf .ne) s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 27 = input / 2 ^ sigma ∧
      t.mem.readW (State.addr (t.sp + 64#32)) 32 = 0#32 ∧
      (∀ j, j < 30 → j ≠ 27 → num t.mem (base + 96#32) (2 * w + 2) j =
        num s.mem (base + 96#32) (2 * w + 2) j) ∧
      (∀ d, d + 8 ≤ 256 → t.mem.readW (off (State.addr base) d) 64 =
        s.mem.readW (off (State.addr base) d) 64) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest opRegs s t := by
  let inv := fun left t => ∃ i, ExponentInv s base capacity w input sigma i left t
  refine WP.loop (M := isa) inv ?_ sigma s ?_
  · intro left u h
    obtain ⟨i, h⟩ := h
    refine WP.mono (exponentHalfStep_ok h.workspace h.ready h.data h.stack h.positive h.bound h.saved h.separate) ?_
    rintro t ⟨readyT, dataT, valueT, savedT, zeroT, arraysT, headerT, frameT, restT⟩
    have value : num t.mem (base + 96#32) (2 * w + 2) 27 = input / 2 ^ (i + 1) := by
      rw [valueT, h.number, Nat.div_div_eq_div_mul, Nat.pow_succ]
    have rest := h.rest.trans restT
    rw [h.rest.sp] at frameT
    have frame := h.frame.trans frameT
    have arrays (j : Nat) (bound : j < 30) (different : j ≠ 27) :=
      (arraysT j bound different).trans (h.arrays j bound different)
    have header (d : Nat) (bound : d + 8 ≤ 256) := (headerT d bound).trans (h.header d bound)
    by_cases last : left = 1
    · left
      have done : i + 1 = sigma := by have := h.remaining; omega
      refine ⟨?_, readyT, dataT, ?_, ?_, arrays, header, frame, rest⟩
      · change some (!t.z) = some false
        simp only [zeroT, last, decide_true, Bool.not_true]
      · rwa [done] at value
      · simpa only [last, Nat.sub_self] using savedT
    · right
      refine ⟨?_, left - 1, by have := h.positive; omega, i + 1, ?_⟩
      · change some (!t.z) = some true
        simp only [zeroT, last, decide_false, Bool.not_false]
      · refine ⟨h.workspace.congr restT.wr, readyT, dataT, ?_, ?_, value, savedT,
          by have := h.remaining; have := h.positive; omega,
          by have := h.positive; omega, by have := h.bound; omega, arrays, header, frame, rest⟩
        · rw [restT.sp]; exact h.stack.congr restT.wr
        · rw [restT.sp]; exact h.separate
  · exact ⟨0, workspace, ready, data, stack, separate, by simpa using number,
      saved, by simp, positive, bound, by intros; rfl, by intros; rfl, Frame.refl _ _, Rest.refl _ _⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
