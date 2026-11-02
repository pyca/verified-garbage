module

public import VerifiedGarbage.Impl.Dsa.X86.CombCore
import VerifiedGarbage.Proof.Dsa.X86.Comb.Call
import VerifiedGarbage.Proof.Dsa.X86.CorePowerLoad
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! Byte-oriented comb calls preserve the retained table across input and output staging. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def callRanges (prepare : Bool) (n output len : Nat) : List (Nat × Nat) :=
  [(0,contextBytes n),(output,len)] ++ if prepare then [(context n,272*n)] else []

theorem corePower_ok {s : State} {base : Addr} {size len expLen n m output : Nat}
    {a b : Pointer} {modulus : Field}
    (supported : Supported n ((expLen+3)/4)) (prepare : Bool)
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved≤size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes≤size)
    (hn : n=(len+7)/8) (h4 : 4≤len) (hmax : len≤384) (hw4 : len%4=0)
    (he4 : 8≤expLen) (he : expLen≤len) (hwe : expLen%4=0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b expLen)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len)=m)
    (hm1 : 1<m) (odd : m%2=1)
    (ho : output+len≤size) (hfar : contextBytes n≤output)
    (sizeComb : (layout n ((expLen+3)/4)).size≤size)
    (sep : output+len≤context n ∨ context n+272*n≤output)
    (H : prepare=false → canonical n ((expLen+3)/4) m
      (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len)) base s.mem) :
    WP isa (power prepare len expLen modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len=Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len)^
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) expLen)%m) ∧
      (prepare=true → canonical n ((expLen+3)/4) m
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len)) base t.mem) ∧
      StackOuts base (s.gpr .esp) (callRanges prepare n output len) s.mem t.mem ∧ Keeps powerClob s t := by
  have L := table_layout supported
  have nw := hs.nowrap
  have cb : contextBytes n≤size := by have := L.apart; have := L.bound; omega
  have hl : len≤8*n := by omega
  have bound (j : Nat) (hj : j<9) : slot n j+8*n≤contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega
  have bounds (j : Nat) (hj : j<9) : slot n j+8*n≤size := by have := bound j hj; omega
  have contextSize : 8*Proof.Dsa.FixedBaseComb.contextWords (layout n ((expLen+3)/4))=272*n := by
    rcases supported with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> rfl
  unfold power
  dsimp only
  rw [←hn]
  refine WP.seq (WP.mono (coreLoadPower_ok hs hz hn h4 hmax hw4 he4 he hwe Rq Ra Rb hm cb)
    fun w ⟨Mw,Aw,Ew,Opre,Ksw⟩ => ?_)
  have Cpre : prepare=false → canonical n ((expLen+3)/4) m (wordsVal w.mem base (slot n 5) n) base w.mem := by
    intro hp
    rw [Aw]
    unfold canonical
    rw [wordsAt_canonical,Opre.wordsVal (.inr (by simpa only [Nat.zero_add] using L.apart)) (by rw [contextSize]; have := L.bound; omega),←wordsAt_canonical]
    exact H hp
  have Wscr := hs.of_keeps Ksw (by decide)
  refine WP.seq (WP.mono (call_ok supported prepare Wscr (by rw [Ksw.1 _ (by decide)]; exact room)
    sizeComb hused Mw hm1 odd Cpre) fun v ⟨⟨Vv,Cv⟩,Ov,Kv⟩ => ?_)
  refine WP.mono (coreStore_ok (Wscr.of_keeps Kv (by decide)) hz hn.symm
    (bounds 6 (by decide)) h4 hl hw4 ho (by have := bound 6 (by decide); omega)) fun t ⟨Vt,Kt,Ot⟩ => ?_
  refine ⟨by rw [Vt,Vv,Aw,Ew],?_,?_,?_⟩
  · intro hp
    unfold canonical
    rw [wordsAt_canonical,Ot.wordsVal (by rw [contextSize]; exact sep.symm) (by rw [contextSize]; have := L.bound; omega),←wordsAt_canonical]
    rw [Aw] at Cv
    exact Cv hp
  · rw [Ksw.1 _ (by decide)] at Ov
    have Of : StackOuts base (s.gpr .esp) (callRanges prepare n output len) w.mem v.mem := Ov.mono (by
      intro r hr
      unfold scratch VG.Impl.Dsa.X86.Pow.scratch at hr
      rcases List.mem_append.mp hr with hr|hr
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl
        · exact ⟨(0,contextBytes n),by simp [callRanges],Nat.le_refl _,by simp [contextBytes,slot,stride]⟩
        · exact ⟨(0,contextBytes n),by simp [callRanges],by omega,by
            have := slot_bound (n := n) (i := 1) (by decide); simp only [stride] at this; omega⟩
      · cases prepare with
        | false => simp at hr
        | true => simp only [ite_true,List.mem_singleton] at hr; subst r
                  exact ⟨(context n,272*n),by simp [callRanges],Nat.le_refl _,Nat.le_refl _⟩)
    exact ((StackOuts.of_outs (Outs.of_outside Opre (by simp [callRanges]))).trans Of).trans
      (StackOuts.of_outs (Outs.of_outside Ot (by simp [callRanges])))
  · exact ((Ksw.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.Dsa.X86.Comb
