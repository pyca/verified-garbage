module

import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Dsa.X86.WorkspaceCall
import VerifiedGarbage.Proof.Dsa.X86.PowBody
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! The ordinary power helper uses the shared workspace-call boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

theorem call_ok {s : State} {base : Addr} {size n e m : Nat}
    (hs : Scr s base size) (room : Room (s.gpr .esp) base size)
    (hz : contextBytes n ≤ size) (hused : VG.Impl.Dsa.Layout.usedBytes ≤ size)
    (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Impl.Dsa.X86.Pow.call n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      StackOuts base (s.gpr .esp) (scratch n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold Impl.Dsa.X86.Pow.call
  let P := fun mem => wordsVal mem base (slot n 0) n=m ∧
    wordsVal mem base (slot n 5) n=wordsVal s.mem base (slot n 5) n ∧
    val32 mem base (slot n 8) e=val32 s.mem base (slot n 8) e
  refine workspaceCall_ok (P := P) (Q := fun mem => wordsVal mem base (slot n 6) n=
      wordsVal s.mem base (slot n 5) n^val32 s.mem base (slot n 8) e%m)
    (bytes := contextBytes n) (name := name n e) hs room hused (body_noSp n e) (body_stackUse n e)
    (scratch_fits hz) ?_ ?_
  · intro mem F
    have vals : ∀ d k, d+4*k≤size → val32 mem base d k=val32 s.mem base d k :=
      fun _ _ hd => frame_val32 room hs.nowrap F hd
    refine ⟨?_,?_,?_⟩
    · rw [wordsVal_eq_val32,vals _ _ (by simp only [contextBytes,slot,stride] at hz ⊢; omega),←wordsVal_eq_val32,hv]
    · rw [wordsVal_eq_val32,wordsVal_eq_val32]
      exact vals _ _ (by simp only [contextBytes,slot,stride] at hz ⊢; omega)
    · exact vals _ _ (by simp only [contextBytes,slot,stride] at hz ⊢; omega)
  · intro v E C ⟨M,G,X⟩
    exact WP.mono (body_ok E C hz hn hn48 he hen M hm1 hodd) fun w ⟨V,O,R,Rd,Wr⟩ =>
      ⟨by rw [V,G,X],O,R,Rd,Wr⟩

end VG.Proof.Dsa.X86.Pow
