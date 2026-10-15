module

public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The SSE registers through code that writes none

Code that writes no vector register and calls nothing keeps the SSE
registers, so that code can keep a general register's value in one. -/

@[expose] public section

namespace VG.X86_64.KeepReg
open VG VG.X86_64

theorem allInstrs_block {p : Instr → Bool} : ∀ (is : List Instr), (Code.block is : Prog isa).allInstrs p = is.all p
  | [] => rfl
  | i :: is => by
    have h := allInstrs_block (p := p) is
    simp only [Code.allInstrs] at h ⊢
    simp only [List.all_cons, h]

theorem execBlock_xmm : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    is.all (fun i => !KeepReg.writesVec i) = true → execBlock isa is s = some (s', t) → s'.xmm = s.xmm
  | [], s, s', t, _, h => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | i :: is, s, s', t, hv, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hv
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact (execBlock_xmm (t := p.2) hv.2 (by rw [hp])).trans (KeepReg.exec_xmm hv.1 h₁)

/-- Code that writes no vector register, and calls nothing, keeps the SSE
registers. -/
theorem Exec.xmm_of {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    c.allInstrs (fun i => !KeepReg.writesVec i) = true → c.noCalls = true → s'.xmm = s.xmm := by
  induction h with
  | block he =>
    intro hv _
    rw [allInstrs_block] at hv
    exact execBlock_xmm hv he
  | seq _ _ ih₁ ih₂ =>
    intro hv hn
    simp only [Code.allInstrs, Code.noCalls, Bool.and_eq_true] at hv hn
    exact (ih₂ hv.2 hn.2).trans (ih₁ hv.1 hn.1)
  | iteT _ _ ih =>
    intro hv hn
    simp only [Code.allInstrs, Code.noCalls, Bool.and_eq_true] at hv hn
    exact ih hv.1 hn.1
  | iteF _ _ ih =>
    intro hv hn
    simp only [Code.allInstrs, Code.noCalls, Bool.and_eq_true] at hv hn
    exact ih hv.2 hn.2
  | loopExit _ _ ih =>
    intro hv hn
    exact ih hv hn
  | loopNext _ _ _ ih₁ ih₂ =>
    intro hv hn
    exact (ih₂ hv hn).trans (ih₁ hv hn)
  | call => intro _ hn; simp [Code.noCalls] at hn
  | frame => intro _ hn; simp [Code.noCalls] at hn

/-- Code that writes no vector register, and calls nothing, keeps the SSE
registers, as a postcondition. -/
theorem WP.keepXmm {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hv : c.allInstrs (fun i => !writesVec i) = true) (hn : c.noCalls = true) :
    WP isa c s fun t => Q t ∧ t.xmm = s.xmm := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.xmm_of he hv hn⟩

/-- The low quadword of what `movq xmm, r64` writes. -/
theorem xmm_lo_append (x : BitVec 64) : ((0 : BitVec 64) ++ x).extractLsb' 0 64 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_zero]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
  exact Nat.mod_eq_of_lt x.isLt

end VG.X86_64.KeepReg
