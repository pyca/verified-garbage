module

import VerifiedGarbage.Proof.Dsa.X86.Comb.Correct
import VerifiedGarbage.Proof.Dsa.X86.Comb.Stack
import VerifiedGarbage.Proof.Dsa.X86.WorkspaceCall
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Mont.WordsCanonical
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Body
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Dsa.ModPowContract
import VerifiedGarbage.Proof.Dsa.X86.Comb.BodyWide

/-! Both comb calls share the ordinary power helper's cdecl frame proof. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem call_ok {n e m size : Nat} {base : Addr} {s : State}
    (h : Supported n e) (prepare : Bool) (hs : Scr s base size)
    (room : Pow.Room (s.gpr .esp) base size) (hz : (layout n e).size≤size)
    (hused : VG.Impl.Dsa.Layout.usedBytes≤size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (H : prepare=false → canonical n e m (wordsVal s.mem base (slot n 5) n) base s.mem) :
    WP isa (VG.Impl.Dsa.X86.Comb.call prepare n e) s fun t =>
      (wordsVal t.mem base (slot n 6) n=
        wordsVal s.mem base (slot n 5) n^val32 s.mem base (slot n 8) e%m ∧
       (prepare=true → canonical n e m (wordsVal s.mem base (slot n 5) n) base t.mem)) ∧
      StackOuts base (s.gpr .esp) (scratch prepare n) s.mem t.mem ∧ Keeps [.eax,.ecx,.edx] s t := by
  unfold VG.Impl.Dsa.X86.Comb.call
  have bounds : slot n 0+8*n≤(layout n e).size ∧ slot n 5+8*n≤(layout n e).size ∧
      slot n 8+4*e≤(layout n e).size ∧
      context n+8*Proof.Dsa.FixedBaseComb.contextWords (layout n e)≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  let P := fun mem => wordsVal mem base (slot n 0) n=m ∧
    wordsVal mem base (slot n 5) n=wordsVal s.mem base (slot n 5) n ∧
    val32 mem base (slot n 8) e=val32 s.mem base (slot n 8) e ∧
    (prepare=false → canonical n e m (wordsVal s.mem base (slot n 5) n) base mem)
  refine workspaceCall_ok (P := P) (Q := fun mem => wordsVal mem base (slot n 6) n=
      wordsVal s.mem base (slot n 5) n^val32 s.mem base (slot n 8) e%m ∧
      (prepare=true → canonical n e m (wordsVal s.mem base (slot n 5) n) base mem))
    (bytes := (layout n e).size) (name := name prepare n e) hs room hused (body_noSp h prepare) (by rw [body_stack h prepare]; decide)
    (fun r hr => Nat.le_trans (scratch_fits h prepare r hr) hz) ?_ ?_
  · intro mem F
    have vals : ∀ d k, d+4*k≤size → val32 mem base d k=val32 s.mem base d k :=
      fun _ _ hd => Pow.frame_val32 room hs.nowrap F hd
    refine ⟨?_,?_,?_,?_⟩
    · rw [wordsVal_eq_val32,vals _ _ (by omega),←wordsVal_eq_val32,hv]
    · rw [wordsVal_eq_val32,wordsVal_eq_val32]
      exact vals _ _ (by omega)
    · exact vals _ _ (by omega)
    · intro hp
      unfold canonical
      rw [wordsAt_canonical,wordsVal_eq_val32,vals _ _ (by omega),←wordsVal_eq_val32,←wordsAt_canonical]
      exact H hp
  · intro v E _ ⟨M,G,X,C⟩
    refine WP.mono (body_wide_ok h prepare E hz M hm odd (by rw [G]; exact C)) fun w ⟨V,Cw,O,R,Rd,Wr⟩ => ?_
    exact ⟨⟨by rw [V,G,X],by rw [G] at Cw; exact Cw⟩,Pow.OutsS.of_outs O,R,Rd,Wr⟩

end VG.Proof.Dsa.X86.Comb
