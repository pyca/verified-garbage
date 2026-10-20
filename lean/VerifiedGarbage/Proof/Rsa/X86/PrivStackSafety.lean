module
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl

import VerifiedGarbage.Proof.Rsa.X86.PrivFnInput
import VerifiedGarbage.Proof.Rsa.X86.PrivNoSp
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Spec.Weierstrass

/-! # Stack bounds and stack-pointer safety of the complete checked private wrapper -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked

theorem privateCode_noSp (v : CrtImpl) : NoSp (privCode v) := by
  intro i hi
  change i ∈ instrs (.frame (.push savedRegisters)
    (.seq (.frame (.alloc VG.Impl.Rsa.X86.PrivChecked.frameBytes)
      (body v.name v.code v.pcName v.pc v.pdName v.pd) (.free VG.Impl.Rsa.X86.PrivChecked.frameBytes))
      (.block restore)) (.pop .ebx 4)) at hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · apply privateInner_noSp v i
    simpa only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] using hi
  · rfl

theorem noSp_allStack {c : Prog isa} (h : NoSp c) : c.all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  have eq : (!isa.writesSp i) = !Taint.clobbers i .esp := by cases i <;> rfl
  rw [eq, h i hi]
  rfl

theorem code_sp (v : CrtImpl) : (privCode v).all (fun i => !isa.writesSp i) = true :=
  noSp_allStack (privateCode_noSp v)

theorem code_stack (v : CrtImpl) : stackUse (privCode v) ≤ stackBytes := by
  have crt := v.stack
  have pc := v.pcStack
  have pd := v.pdStack
  have bound : stackUse (body v.name v.code v.pcName v.pc v.pdName v.pd) ≤ 24 := by
    simp only [body, check, tail, compareBytes, release, releaseLoop, stackUse, Nat.max_le]
    repeat apply And.intro
    all_goals omega
  simp only [privCode, code, stackUse, VG.X86.frameBytes, List.length_cons, List.length_nil,
    VG.Impl.Rsa.X86.PrivChecked.frameBytes, stackBytes]
  omega
end VG.Proof.Rsa.X86.PrivChecked
