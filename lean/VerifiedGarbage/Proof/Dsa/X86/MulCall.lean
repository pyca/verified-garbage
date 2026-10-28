module

import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Dsa.X86.WorkspaceCall
import VerifiedGarbage.Proof.Dsa.X86.MulBody
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
public import VerifiedGarbage.Impl.Dsa.X86.Arith
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! The ordinary product helper uses the shared workspace-call boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Mul
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Arith

theorem body_noSp (n : Nat) : NoSp (mulBody n) := NoSp.of_all rfl

theorem body_stackUse (n : Nat) : stackUse (mulBody n) = 0 := rfl

theorem body_spSafe (n : Nat) : (mulBody n).allInstrs (fun i => !isa.writesSp i) = true := rfl

theorem call_ok {s : State} {base : Addr} {size n m : Nat}
    (hs : Scr s base size) (room : Pow.Room (s.gpr .esp) base size)
    (hz : contextBytes n ≤ size) (hused : VG.Impl.Dsa.Layout.usedBytes ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (mulCall n) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n * wordsVal s.mem base (slot n 8) n % m ∧
      StackOuts base (s.gpr .esp) (VG.Impl.Dsa.X86.Pow.scratch n) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t := by
  unfold mulCall
  let P := fun mem => wordsVal mem base (slot n 0) n = m ∧
    wordsVal mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n ∧
    wordsVal mem base (slot n 8) n = wordsVal s.mem base (slot n 8) n
  refine workspaceCall_ok (P := P) (Q := fun mem => wordsVal mem base (slot n 6) n =
      wordsVal s.mem base (slot n 5) n * wordsVal s.mem base (slot n 8) n % m)
    (bytes := contextBytes n) (name := mulName n) hs room hused (body_noSp n)
    (by rw [body_stackUse]; decide) (Pow.scratch_fits hz) ?_ ?_
  · intro mem F
    have vals : ∀ d k, d + 4 * k ≤ size → val32 mem base d k = val32 s.mem base d k :=
      fun _ _ hd => Pow.frame_val32 room hs.nowrap F hd
    refine ⟨?_, ?_, ?_⟩
    · rw [wordsVal_eq_val32, vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega),
        ← wordsVal_eq_val32, hv]
    · rw [wordsVal_eq_val32, wordsVal_eq_val32]
      exact vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega)
    · rw [wordsVal_eq_val32, wordsVal_eq_val32]
      exact vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega)
  · intro v E _ ⟨M, A, B⟩
    exact WP.mono (body_ok E hz hn hn48 M hm1 hodd) fun w ⟨V, O, R, Rd, Wr⟩ =>
      ⟨by rw [V, A, B], Pow.OutsS.of_outs O, R, Rd, Wr⟩

end VG.Proof.Dsa.X86.Mul
