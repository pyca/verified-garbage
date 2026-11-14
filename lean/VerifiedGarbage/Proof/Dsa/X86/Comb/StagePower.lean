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
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame

/-! ### `Dsa.X86.Comb.CorePower`, which only this module used -/

section

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
  have cb : contextBytes n≤size := by have := L.apart; have := L.bound; omega_using [ho, hfar]
  have hl : len≤8*n := by omega_using [hn]
  have bound (j : Nat) (hj : j<9) : slot n j+8*n≤contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [H]
  have bounds (j : Nat) (hj : j<9) : slot n j+8*n≤size := by have := bound j hj; omega_using [cb, this]
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
    rw [wordsAt_canonical,Opre.wordsVal (.inr (by simpa only [Nat.zero_add] using L.apart)) (by rw [contextSize]; have := L.bound; omega_using [hz, hused, hn, h4, hmax, hw4, he4, he, hwe, ho, hfar, sizeComb, sep, nw, cb, hl, contextSize, this]),←wordsAt_canonical]
    exact H hp
  have Wscr := hs.of_keeps Ksw (by decide)
  refine WP.seq (WP.mono (call_ok supported prepare Wscr (by rw [Ksw.1 _ (by decide)]; exact room)
    sizeComb hused Mw hm1 odd Cpre) fun v ⟨⟨Vv,Cv⟩,Ov,Kv⟩ => ?_)
  refine WP.mono (coreStore_ok (Wscr.of_keeps Kv (by decide)) hz hn.symm
    (bounds 6 (by decide)) h4 hl hw4 ho (by have := bound 6 (by decide); omega_using [hfar, this])) fun t ⟨Vt,Kt,Ot⟩ => ?_
  refine ⟨by rw [Vt,Vv,Aw,Ew],?_,?_,?_⟩
  · intro hp
    unfold canonical
    rw [wordsAt_canonical,Ot.wordsVal (by rw [contextSize]; exact sep.symm) (by rw [contextSize]; have := L.bound; omega_using [hz, hused, hn, h4, hmax, hw4, he4, he, hwe, ho, hfar, sizeComb, sep, nw, cb, hl, contextSize, this]),←wordsAt_canonical]
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
        · exact ⟨(0,contextBytes n),by simp [callRanges],by omega_using [],by
            have := slot_bound (n := n) (i := 1) (by decide); simp only [stride] at this; omega⟩
      · cases prepare with
        | false => simp at hr
        | true => simp only [ite_true,List.mem_singleton] at hr; subst r
                  exact ⟨(context n,272*n),by simp [callRanges],Nat.le_refl _,Nat.le_refl _⟩)
    exact ((StackOuts.of_outs (Outs.of_outside Opre (by simp [callRanges]))).trans Of).trans
      (StackOuts.of_outs (Outs.of_outside Ot (by simp [callRanges])))
  · exact ((Ksw.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.Dsa.X86.Comb

end

end


/-! Integrate comb powers into the byte-oriented DSA schedule with their full footprint. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem supported_widths {pLen qLen : Nat} (H : Spec.Dsa.lengthsValid pLen qLen) :
    Supported ((pLen+7)/8) ((qLen+3)/4) := by
  unfold Spec.Dsa.lengthsValid at H
  rcases H with ⟨rfl,rfl⟩|⟨rfl,(rfl|rfl|rfl)⟩|⟨rfl,rfl⟩ <;> unfold Supported <;> decide

theorem stagePower_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (prepare : Bool) (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen+7)/8) a pLen)
    (Rb : OperandReady s base ((pLen+7)/8) b qLen)
    (ho : output∈Layout.wideValues)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size)
    (H : prepare=false → canonical ((pLen+7)/8) ((qLen+3)/4) p
      (operandValue s base a pLen) base s.mem) :
    WP isa (power prepare pLen qLen .p a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      Spec.Rsa.bytesAt t.mem (off base output) pLen = Spec.Dsa.encodeBE pLen
        (operandValue s base a pLen ^ operandValue s base b qLen % p) ∧
      (prepare=true → canonical ((pLen+7)/8) ((qLen+3)/4) p
        (operandValue s base a pLen) base t.mem) ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s ∧
      ScheduleFrame base size s t ∧
      StackOuts base (s.gpr .esp) (callRanges prepare ((pLen+7)/8) output pLen) s.mem t.mem := by
  have L := M.lengths
  have Al := M.aligned
  have sup := supported_widths M.widths
  have W : 14944≤output ∧ output+384≤15712 := by
    simp only [Layout.wideValues,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl <;> decide
  have fit := M.wideFit ho
  have np : (pLen+7)/8≤48 := by omega_using [L]
  have sep : output+pLen≤context ((pLen+7)/8) ∨ context ((pLen+7)/8)+272*((pLen+7)/8)≤output := by
    rcases sup with ⟨hn,_⟩|⟨hn,_⟩|⟨hn,_⟩|⟨hn,_⟩|⟨hn,_⟩ <;> rw [hn]
    · change output+pLen≤9216 ∨ 13568≤output; omega_using [W]
    · change output+pLen≤16384 ∨ 25088≤output; omega_using [L, W]
    · change output+pLen≤16384 ∨ 25088≤output; omega_using [L, W]
    · change output+pLen≤16384 ∨ 25088≤output; omega_using [L, W]
    · change output+pLen≤16384 ∨ 29440≤output; omega_using [L, W]
  refine WP.mono (corePower_ok sup prepare M.scr M.saved M.room M.extent rfl
    (by omega_using [L]) (by omega_using [L]) Al.1 (by omega_using [L]) (by omega_using [L]) Al.2 M.pReady Ra Rb M.pValue
    M.pLarge M.pOdd (Nat.le_trans fit M.extent)
    (by have := VG.Proof.Dsa.X86.Layout.context_bound np; change _≤7048 at this; omega_using [W, this])
    sizeComb sep H) fun t ⟨V,C,O,K⟩ => ?_
  have bounds : ∀ r∈callRanges prepare ((pLen+7)/8) output pLen, r.1+r.2≤size := by
    intro r hr
    unfold callRanges at hr
    rcases List.mem_append.mp hr with hr|hr
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · simpa only [Nat.zero_add] using M.context np
      · exact Nat.le_trans fit M.extent
    · cases prepare with
      | false => simp at hr
      | true => simp only [ite_true,List.mem_singleton] at hr; subst r
                exact sizeComb
  have unchanged (d : Nat) (lo : 8192≤d) (hi : d+4≤8272) :
      ∀ r∈callRanges prepare ((pLen+7)/8) output pLen, d+4≤r.1 ∨ r.1+r.2≤d := by
    intro r hr
    unfold callRanges at hr
    rcases List.mem_append.mp hr with hr|hr
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · have B := VG.Proof.Dsa.X86.Layout.context_bound np
        change _≤7048 at B; simp only [Nat.zero_add]; omega_using [lo, B]
      · change 14944≤output ∧ output+384≤15712 at W
        exact .inl (by omega)
    · cases prepare with
      | false => simp at hr
      | true => simp only [ite_true,List.mem_singleton] at hr; subst r
                exact .inl (by unfold context; split <;> omega_using [hi])
  have F := ScheduleFrame.of_ranges K O bounds (fun f _ => unchanged _
    (VG.Proof.Dsa.X86.Layout.field_bounds f).1 (by
      have B := (VG.Proof.Dsa.X86.Layout.field_bounds f).2
      change _≤8256 at B; omega_using [B])) (fun p hp => unchanged _
    (by have := (saved_bounds hp).1; omega_using [this]) (saved_bounds hp).2)
  refine ⟨F.moduli M,V,C,?_,F,O⟩
  have Vmask := O.val32 (unchanged (Layout.field .mask) (by decide) (by decide)) (by decide : Layout.field .mask+4*1≤usedBytes)
  apply BitVec.eq_of_toNat_eq
  simpa only [flagW,val32,Nat.mul_zero,Nat.add_zero] using Vmask

theorem stagePrivate_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen+7)/8) a pLen)
    (Rb : OperandReady s base ((pLen+7)/8) b qLen)
    (ho : output∈Layout.wideValues)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size)
    (C : canonical ((pLen+7)/8) ((qLen+3)/4) p (operandValue s base a pLen) base s.mem) :
    WP isa (power false pLen qLen .p a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output pLen
        (operandValue s base a pLen ^ operandValue s base b qLen % p) := by
  refine WP.mono (stagePower_ok false M Ra Rb ho sizeComb (fun _ => C)) fun t ⟨Mt,V,_,_,F,O⟩ => ?_
  have O' : StackOuts base (s.gpr .esp) [(0,contextBytes ((pLen+7)/8)),(output,pLen)] s.mem t.mem := by
    simpa only [callRanges,Bool.false_eq_true,ite_false,List.append_nil] using O
  exact ⟨Mt,⟨StageFrame.of_stackFrame F.keeps (by decide) O' (by have := M.lengths; omega_using [this]),V⟩⟩

end VG.Proof.Dsa.X86.Comb
