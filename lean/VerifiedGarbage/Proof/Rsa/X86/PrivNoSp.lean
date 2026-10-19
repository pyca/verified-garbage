module

public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # Checked private RSA preserves the stack pointer inside its frames -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked

theorem privateBody_noSp (v : CrtImpl) :
    NoSp (body v.name v.code v.pcName v.pc v.pdName v.pd) := by
  unfold body check
  exact .seq' (.of_all (by decide +kernel)) (.seq' (.call' v.noSp)
    (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.pcNoSp)
      (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.pdNoSp)
        (.of_all (by decide +kernel)))))))

theorem privateAllocation_noSp (v : CrtImpl) :
    NoSp (.frame (.alloc frameBytes)
      (body v.name v.code v.pcName v.pc v.pdName v.pd) (.free frameBytes)) := by
  intro i hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact privateBody_noSp v i hi
  · rfl

theorem privateInner_noSp (v : CrtImpl) :
    NoSp (.seq (.frame (.alloc frameBytes)
      (body v.name v.code v.pcName v.pc v.pdName v.pd) (.free frameBytes)) (.block restore)) :=
  .seq' (privateAllocation_noSp v) (.of_all (by decide +kernel))
end VG.Proof.Rsa.X86.PrivChecked
