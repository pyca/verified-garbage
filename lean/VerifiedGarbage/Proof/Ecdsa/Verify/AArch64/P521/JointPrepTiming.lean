module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.PrepTiming
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64

theorem prepare_relCT {base : Addr}
 (h7 : PubNafWide.PrepChecks P521Joint.KG (p521.sl U))
 (h5 : PubNaf.PrepChecks P521Joint.K (p521.sl V)) :
 RelCT isa (fun s t=>Scr s base 8192 ∧ Scr t base 8192 ∧ s.sp=t.sp ∧
  sv p521 base s U=sv p521 base t U ∧ sv p521 base s V=sv p521 base t V)
 (.seq P521Joint.prep7 (PubNaf.prep P521Joint.K (p521.sl V))) (fun _ _=>True) := by
 intro s t ts tt s' t' ⟨hs,ht,sp,hu,hv⟩ es et
 cases es with | seq gs ps =>
 cases et with | seq gt pt =>
 have regs:=PubNaf.regs_ok9 9 (by decide) (by decide)
 have tr:=PubNafWide.prep7_relCT P521Joint.KG regs (by decide) (by decide) (by decide) (by decide) h7
   _ _ _ _ _ _ ⟨hs,ht,sp,hu⟩ gs gt
 obtain ⟨_,_,xs,ss,_,_,ks,us⟩:=PubNafWide.prep_ok P521Joint.KG (Or.inr rfl) regs hs
   (src:=p521.sl U) (by decide) (by decide) (by decide) (by decide)
 obtain ⟨_,_,xt,st,_,_,kt,ut⟩:=PubNafWide.prep_ok P521Joint.KG (Or.inr rfl) regs ht
   (src:=p521.sl U) (by decide) (by decide) (by decide) (by decide)
 obtain ⟨_,rfl⟩:=Exec.det gs xs
 obtain ⟨_,rfl⟩:=Exec.det gt xt
 have vv : wordsVal _ base (p521.sl V) 9=wordsVal _ base (p521.sl V) 9 :=
   (us.wordsVal (Or.inl (by decide)) (by decide)).trans
    (hv.trans (ut.wordsVal (Or.inl (by decide)) (by decide)).symm)
 have tp:=PubNaf.prep_relCT P521Joint.K regs (by decide) (by decide) (by decide) (by decide) h5
   _ _ _ _ _ _ ⟨ss,st,ks.sp.trans (sp.trans kt.sp.symm),vv⟩ ps pt
 exact ⟨by rw [tr.1,tp.1],trivial⟩
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
