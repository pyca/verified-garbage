module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.RvBatchGcd
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Time
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.TimeCheck
import VerifiedGarbage.Proof.Rsa.X86.RvBatchTimeCheck
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.X86.RvGcdSet
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.FrameBase

/-! # Public selection and constant-time execution of recovery GCD -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)

 theorem batchBody_trace {g : Geo} {s0 t0 s t : State} {V W : Nat → Nat} {m y z : Nat}
    (h : KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s)
    (j : KS g t0 (AG g.w m z) liveG (fun _ => 0) [] W [sMask] t) (odd : m%2=1)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (check : (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset g.w 15))
      (VG.Impl.Rsa.X86.GcdBatch.body g.w)
      hint).isSome=true)
    {tr ur : List Leak} {sf tf : State}
    (es : Exec isa (VG.Impl.Rsa.X86.GcdBatch.body g.w) s tr sf)
    (et : Exec isa (VG.Impl.Rsa.X86.GcdBatch.body g.w) t ur tf) : tr=ur := by
  apply GcdBatch.body_trace h.ws.workspace j.ws.workspace
    (by have := h.lower; simp only [Geo.w,width]; omega) h.ws.wle
    (by rw [GcdBatch.offset_arr]; exact Nat.le_trans (arr_mono (by decide : 15≤nArr)) h.ws.fits)
    (h.sp.trans j.sp.symm) _ _ check es et
  · rw [GcdBatch.offset_arr]
    change num s.mem g.B g.w aM%2=1
    rw [h.arrs aM (by simp [liveG])]
    exact odd
  · rw [GcdBatch.offset_arr]
    change num t.mem g.B g.w aM%2=1
    rw [j.arrs aM (by simp [liveG])]
    exact odd

 theorem batchChoose_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {V W : Nat → Nat}
    {m y z len words : Nat} {fallback : Prog isa}
    (odd : m%2=1) (small : len<2^32)
    (width : 2*Spec.Rsa.modulusWords (len+8)=words)
    (choiceCheck : (VG.Taint.check sseTaint τA (.block (VG.Impl.Rsa.X86.GcdBatch.choice len))
      (VG.Taint.hintOf sseTaint τA (.block (VG.Impl.Rsa.X86.GcdBatch.choice len)))).isSome=true)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (bodyCheck : (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset words 15))
      (VG.Impl.Rsa.X86.GcdBatch.body words)
      hint).isSome=true)
    (other : RelCT isa (fun s t =>
      KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s ∧
      KS g t0 (AG g.w m z) liveG (fun _ => 0) [] W [sMask] t) fallback (fun _ _ => True)) :
    RelCT isa (fun s t =>
      KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s ∧
      KS g t0 (AG g.w m z) liveG (fun _ => 0) [] W [sMask] t)
      (VG.Impl.Rsa.X86.GcdBatch.choose len words fallback) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.GcdBatch.choose
  refine VG.RelCT.seq (R := fun (s t : State) =>
    (KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s ∧
      s.zf=some (decide (g.args 5=BitVec.ofNat 32 len))) ∧
    (KS g t0 (AG g.w m z) liveG (fun _ => 0) [] W [sMask] t ∧
      t.zf=some (decide (g.args 5=BitVec.ofNat 32 len))))
    (pub_relCT pg choiceCheck (fun _ h => KS.stage h) (fun _ h => KS.stage h)
      (fun _ h => batchChoice_ok len h) (fun _ h => batchChoice_ok len h)) ?_
  refine VG.RelCT.ite (fun s t ⟨⟨_,cs⟩,⟨_,ct⟩⟩ => by change s.zf=t.zf; rw [cs,ct]) ?_ ?_
  · intro s t tr ur sf tf ⟨⟨⟨hs,cs⟩,⟨ht,ct⟩⟩,yes⟩ es et
    have e : g.args 5=BitVec.ofNat 32 len := by
      change s.zf=some true at yes
      rw [cs] at yes
      exact of_decide_eq_true (Option.some.inj yes)
    have w := hs.batchWidth
    rw [e,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,width] at w
    rw [←w] at bodyCheck es et
    exact ⟨batchBody_trace hs ht odd bodyCheck es et,trivial⟩
  · exact other.mono (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ _ => trivial)

 theorem batchGcd_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {V W : Nat → Nat}
    {m y z : Nat} (odd : m%2=1) :
    RelCT isa (fun s t =>
      KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s ∧
      KS g t0 (AG g.w m z) liveG (fun _ => 0) [] W [sMask] t)
      (VG.Impl.Rsa.X86.GcdBatch.dispatch
        (VG.Impl.Rsa.X86.KeyRt.gcd VG.Impl.Rsa.X86.RecoverRt.nar)) (fun _ _ => True) := by
  obtain ⟨_, body66_check⟩ := GcdBatch.body66_check
  obtain ⟨_, body98_check⟩ := GcdBatch.body98_check
  obtain ⟨_, body130_check⟩ := GcdBatch.body130_check
  unfold VG.Impl.Rsa.X86.GcdBatch.dispatch
  exact batchChoose_relCT (len := 256) (words := 66) pg odd (by decide) (by decide) batchChoice256Check body66_check
    (batchChoose_relCT (len := 384) (words := 98) pg odd (by decide) (by decide) batchChoice384Check body98_check
      (batchChoose_relCT (len := 512) (words := 130) pg odd (by decide) (by decide) batchChoice512Check body130_check
        (pub_relCT' pg scalarGcdCheck.choose_spec (fun _ h => KS.stage h) (fun _ h => KS.stage h))))

 theorem factors_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {A B V W : Nat → Nat}
    {m y z : Nat} (modA : A aN=m) (modB : B aN=m)
    (valueA : A mY=y) (valueB : B mY=z) (zeroA : A aZ=0) (zeroB : B aZ=0)
    (oneA : A aOne=1) (oneB : B aOne=1) (odd : m%2=1) (hm : 1<m) :
    RelCT isa (fun s t =>
      KS g s0 A [mY,aN,aZ,aOne] (fun _ => 0) [] V [sMask] s ∧
      KS g t0 B [mY,aN,aZ,aOne] (fun _ => 0) [] W [sMask] t)
      VG.Impl.Rsa.X86.RecoverRt.factors (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.factors
  simp only [seqs]
  refine VG.RelCT.seq (pub_relCT pg gcdSetCheck.choose_spec (fun _ h => KS.stage h) (fun _ h => KS.stage h)
    (fun _ h => gcdSet_ok h modA valueA zeroA oneA)
    (fun _ h => gcdSet_ok h modB valueB zeroB oneB)) ?_
  refine VG.RelCT.seq (stage_relCT (batchGcd_relCT pg odd)
    (fun _ h => batchGcd_ok h odd hm) (fun _ h => batchGcd_ok h odd hm)) ?_
  exact pub_relCT' pg factorTailCheck.choose_spec (fun _ h => KS.stage h) (fun _ h => KS.stage h)

end VG.Proof.Rsa.X86.Recover
