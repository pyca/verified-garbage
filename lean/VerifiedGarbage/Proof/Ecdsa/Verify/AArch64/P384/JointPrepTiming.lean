module
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide9Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide9
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdsa.AArch64

theorem prepare_relCT {base : Addr}
 (h9 : PubNafWide.Prep9Checks P384Joint.KG (p384.sl U))
 (h5 : PubNaf.PrepChecks P384Joint.K (p384.sl V)) :
 RelCT isa (fun s t=>Scr s base 8192 ∧ Scr t base 8192 ∧ s.sp=t.sp ∧
  sv p384 base s U=sv p384 base t U ∧ sv p384 base s V=sv p384 base t V)
 (.seq P384Joint.prep9 (PubNaf.prep P384Joint.K (p384.sl V))) (fun _ _=>True) := by
 intro s t ts tt s' t' ⟨hs,ht,sp,hu,hv⟩ es et
 cases es with | seq gs ps =>
 cases et with | seq gt pt =>
 have regs:=PubNaf.regs_ok9 6 (by decide) (by decide)
 have tr:=PubNafWide.prep9_relCT P384Joint.KG regs (by decide) (by decide) (by decide) (by decide) h9
   _ _ _ _ _ _ ⟨hs,ht,sp,hu⟩ gs gt
 obtain ⟨_,_,xs,⟨ss,_⟩,ks,us⟩:=PubNafWide.prep9_ok P384Joint.KG regs hs
   (src:=p384.sl U) (by decide) (by decide) (by decide) (by decide)
 obtain ⟨_,_,xt,⟨st,_⟩,kt,ut⟩:=PubNafWide.prep9_ok P384Joint.KG regs ht
   (src:=p384.sl U) (by decide) (by decide) (by decide) (by decide)
 obtain ⟨_,rfl⟩:=Exec.det gs xs
 obtain ⟨_,rfl⟩:=Exec.det gt xt
 have vv : wordsVal _ base (p384.sl V) 6=wordsVal _ base (p384.sl V) 6 :=
   (us.wordsVal (Or.inl (by decide)) (by decide)).trans
    (hv.trans (ut.wordsVal (Or.inl (by decide)) (by decide)).symm)
 have tp:=PubNaf.prep_relCT P384Joint.K regs (by decide) (by decide) (by decide) (by decide) h5
   _ _ _ _ _ _ ⟨ss,st,ks.sp.trans (sp.trans kt.sp.symm),vv⟩ ps pt
 exact ⟨by rw [tr.1,tp.1],trivial⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
