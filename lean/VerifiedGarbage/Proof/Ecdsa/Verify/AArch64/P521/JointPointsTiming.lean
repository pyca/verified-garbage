module
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSource
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrep
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

structure JointWinPublic (base T : Addr) (P : Point p521.C) (u v : Nat) (s t : State) : Prop where
 win : NafWinPublic p521 base P v s t
 leftU : sv p521 base s U=u
 rightU : sv p521 base t U=u
 sourceLeft : FixedGenerator p521.C base 8192 (G p521.C) T s
 sourceRight : FixedGenerator p521.C base 8192 (G p521.C) T t

theorem jointMul_relCT (hc : CfgOk p521) (hC : Law p521.C)
 (hO : PrimeOrder p521.C) (hn17 : 17≤p521.C.n)
 (h7 : PubNafWide.PrepChecks P521Joint.KG (p521.sl U))
 (h5 : PubNaf.PrepChecks P521Joint.K (p521.sl V))
 (hwin : WindowChecks P521Joint.K)
 (mixed : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D)
 {base T : Addr} {P : Point p521.C} {u v : Nat} (hP : onCurve p521.C P=true) :
 RelCT isa (JointWinPublic base T P u v) P521Joint.points
 (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
 rw [P521Joint.points]
 apply RelCT.assoc
 intro s t ts tt s' t' h es et
 obtain ⟨_,fs⟩:=h.win.left.fixed
 obtain ⟨_,ft⟩:=h.win.right.fixed
 cases es with | seq ps ws =>
 cases et with | seq pt wt =>
 have he:=(prepare_relCT h7 h5 _ _ _ _ _ _
   ⟨h.win.left.scr,h.win.right.scr,h.win.sp,h.leftU.trans h.rightU.symm,
     h.win.left.scalar.trans h.win.right.scalar.symm⟩ ps pt).1
 obtain ⟨_,_,xs,ss,ms,Fs,vs,sps,us,rs,ws',_,zs,gs⟩:=
   prepare_ok hc hC h.win.left.scr fs h.win.left.px h.win.left.py h.win.left.rep
 obtain ⟨_,rfl⟩:=Exec.det ps xs
 obtain ⟨_,_,xt,st,mt,Ft,vt,spt,ut,rt,wt',_,zt,gt⟩:=
   prepare_ok hc hC h.win.right.scr ft h.win.right.px h.win.right.py h.win.right.rep
 obtain ⟨_,rfl⟩:=Exec.det pt xt
 rw [h.win.left.scalar] at Fs
 rw [h.win.right.scalar] at Ft
 rw [h.leftU] at gs
 rw [h.rightU] at gt
 have Is : Inv P521Joint.K.M base 8192 p521.C.p (·∈winSlots P521Joint.K) (winRo P521Joint.K)
   (tmv p521.C P521Joint.K.M.n base _) _ := ⟨ss,ms,winRo_slots _,Fs.ro_lt,fun _ _=>rfl⟩
 have It : Inv P521Joint.K.M base 8192 p521.C.p (·∈winSlots P521Joint.K) (winRo P521Joint.K)
   (tmv p521.C P521Joint.K.M.n base _) _ := ⟨st,mt,winRo_slots _,Ft.ro_lt,fun _ _=>rfl⟩
 have pair : FieldPair P521Joint.K.M base 8192 p521.C.p (·∈winSlots P521Joint.K) (winRo P521Joint.K) _ _ _ :=
   ⟨Is,It.congr_env (by
     intro x hx
     simp only [show P521Joint.K.M.n=p521.n from rfl]
     exact (vt x hx).trans ((h.win.fields x hx).symm.trans (vs x hx).symm)),
    sps.trans (h.win.sp.trans spt.symm)⟩
 have vb : v<2^(64*P521Joint.K.M.n) := by
   rw [←h.win.left.scalar,show P521Joint.K.M.n=p521.n from rfl]
   exact wordsVal_lt ..
 have ub : u<2^(64*P521Joint.K.M.n) := by
   rw [←h.leftU,show P521Joint.K.M.n=p521.n from rfl]
   exact wordsVal_lt ..
 have zs':=zs
 have zt':=zt
 simp only [packedQ,Cfg.packedNafQ,Cfg.winCfg,Cfg.pt] at zs' zt'
 rw [←show P521Joint.K.M.n=p521.n from rfl] at zs' zt'
 have genS : GeneratorInput p521.C base T (G p521.C) u _ :=
   ⟨h.sourceLeft.unch us (by decide) rs ws' (Exec.syms ps),gs,zs'⟩
 have genT : GeneratorInput p521.C base T (G p521.C) u _ :=
   ⟨h.sourceRight.unch ut (by decide) rt wt' (Exec.syms pt),gt,zt'⟩
 have one : toM p521.C.p (2^(64*P521Joint.K.M.n)) (p521.mont 1)=1 := by
   rw [show P521Joint.K.M.n=p521.n from rfl,toM_cmont hc.toBaseCfgOk]; rfl
 obtain ⟨hw,post⟩:=jointWindow_relCT (packedNafLay hc rfl)
   (unitMod_pow_two hc.p_odd (64*P521Joint.K.M.n)) hC hc.am3 (by simpa only [show P521Joint.K.M.n=p521.n from rfl] using hc.p_lt)
   (Nat.mod_lt _ (by have := hc.p_ge; omega)) one hwin mixed hO hn17 hP hc.onG vb ub zs'
   _ _ _ _ _ _ ⟨pair,⟨ss,ms,Fs⟩,⟨st,mt,Ft⟩,genS,genT⟩ ws wt
 exact ⟨by rw [he,hw],post⟩
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
