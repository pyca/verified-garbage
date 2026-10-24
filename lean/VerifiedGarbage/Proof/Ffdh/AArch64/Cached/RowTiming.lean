module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.DigitTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectionTiming
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! One complete comb row is constant time for independent secret exponents. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def RowReady (q : DigitPublic) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E (q.i+1) s ∧ Spec.Rsa.os2ip bs<2^q.p.N

def RowDigit (q : DigitPublic) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E (q.i+1) s ∧ Spec.Rsa.os2ip bs<2^q.p.N ∧
 word s.mem q.p.B (8*sD)=BitVec.ofNat 64 (VG.Proof.Rsa.FixedBaseComb.digit q.p.N (Spec.Rsa.os2ip bs) q.i)

def RowProduct (q : DigitPublic) (s : State) : Prop :=
 ∃ bs E F, Running q.p bs E (q.i+1) s ∧ Spec.Rsa.os2ip bs<2^q.p.N ∧
 wv s.mem q.p.B (slot q.p.w 5) q.p.w=Spec.Rsa.powMod q.p.G F q.p.P*2^(64*q.p.w)%q.p.P

def digitWs (q : DigitPublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

theorem row_ct (M : Mont) : RelCT isa (Two RowReady) (Comb.step M.mm) (fun _ _ => True) := by
 unfold Comb.step
 refine RelCT.seq (two_post (Ψ:=RowReady)
  (two_map digitWs (fun q s h => by obtain ⟨bs,E,h,_⟩:=h;exact ⟨q.p.mi,h.power.good,q.p.room⟩)
   (M.ct (by simp [MmUse,Public.aY] : MmUse 6 6 6))) ?_) ?_
 · rintro q s ⟨bs,E,h,bound⟩
   exact WP.mono (running_square M h) fun _ h => ⟨bs,2*E,h,bound⟩
 · refine RelCT.seq (two_post (Ψ:=RowDigit)
    (two_map id (fun _ _ h => by obtain ⟨bs,E,h,_⟩:=h;exact ⟨bs,E,h⟩) digit_ct) ?_) ?_
   · rintro q s ⟨bs,E,h,bound⟩
     refine WP.mono (running_digit h (h.reads.length ▸ q.size) (h.reads.length ▸ q.width) q.positions bound) ?_
     rintro t ⟨run,digit⟩
     exact ⟨bs,E,run,bound,digit⟩
   · refine RelCT.seq (two_post (Ψ:=RowProduct)
      (two_map (fun q : DigitPublic => q.p) (fun q s h => by
       obtain ⟨bs,E,h,_,digit⟩:=h
       exact ⟨bs,E,q.i+1,_,h,VG.Proof.Rsa.FixedBaseComb.digit_lt _ _ _,digit⟩) selection_ct) ?_) ?_
     · rintro q s ⟨bs,E,h,bound,digit⟩
       refine WP.mono (running_select h (VG.Proof.Rsa.FixedBaseComb.digit_lt _ _ _) digit) ?_
       rintro t ⟨run,selected⟩
       exact ⟨bs,E,_,run,bound,selected⟩
     · refine RelCT.seq (two_post (Ψ:=RowReady)
        (two_map digitWs (fun q s h => by obtain ⟨bs,E,F,h,_,_⟩:=h;exact ⟨q.p.mi,h.power.good,q.p.room⟩)
         (M.ct (by simp [MmUse,Public.aY,Public.aXm] : MmUse 6 6 5))) ?_)
        (two_taint [.x0] ?_ (by taint_decide))
       · rintro q s ⟨bs,E,F,h,bound,selected⟩
         exact WP.mono (running_product M h selected) fun _ h => ⟨bs,E+F,h,bound⟩
       · rintro q s t ⟨bs,E,hs,_⟩ ⟨bt,F,ht,_⟩ r hr
         have : r= .x0 := by simpa using hr
         subst r
         exact hs.power.good.x0.trans ht.power.good.x0.symm

end VG.Proof.Ffdh.AArch64.Cached
