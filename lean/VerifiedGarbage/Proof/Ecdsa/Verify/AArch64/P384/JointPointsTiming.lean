module
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointPrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointWindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSource
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide9Timing
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointPrep
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.AArch64.Syms
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass

structure JointWinPublic (base T : Addr) (P : Point p384.C) (u v : Nat) (s t : State) : Prop where
 win : NafWinPublic p384 base P v s t
 leftU : sv p384 base s U=u
 rightU : sv p384 base t U=u
 sourceLeft : FixedGenerator p384.C base 8192 (G p384.C) T s
 sourceRight : FixedGenerator p384.C base 8192 (G p384.C) T t

theorem jointMul_relCT (hc : CfgOk p384) (hC : Law p384.C)
 (hO : PrimeOrder p384.C) (hn17 : 17≤p384.C.n)
 (h9 : PubNafWide.Prep9Checks P384Joint.KG (p384.sl U))
 (h5 : PubNaf.PrepChecks P384Joint.K (p384.sl V))
 (hwin : WindowChecks P384Joint.K)
 (hD : ∀ base, DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) P384Joint.double)
 (mixed : JacMixedChecks P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D)
 {base T : Addr} {P : Point p384.C} {u v : Nat} (hP : onCurve p384.C P=true) :
 RelCT isa (JointWinPublic base T P u v) P384Joint.points
 (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
 rw [P384Joint.points]
 apply RelCT.assoc
 intro s t ts tt s' t' h es et
 obtain ⟨_,fs⟩:=h.win.left.fixed
 obtain ⟨_,ft⟩:=h.win.right.fixed
 cases es with | seq ps ws =>
 cases et with | seq pt wt =>
 have he:=(prepare_relCT h9 h5 _ _ _ _ _ _
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
 have Is : Inv P384Joint.K.M base 8192 p384.C.p (·∈winSlots P384Joint.K) (winRo P384Joint.K)
   (tmv p384.C P384Joint.K.M.n base _) _ := ⟨ss,ms,winRo_slots _,Fs.ro_lt,fun _ _=>rfl⟩
 have It : Inv P384Joint.K.M base 8192 p384.C.p (·∈winSlots P384Joint.K) (winRo P384Joint.K)
   (tmv p384.C P384Joint.K.M.n base _) _ := ⟨st,mt,winRo_slots _,Ft.ro_lt,fun _ _=>rfl⟩
 have pair : FieldPair P384Joint.K.M base 8192 p384.C.p (·∈winSlots P384Joint.K) (winRo P384Joint.K) _ _ _ :=
   ⟨Is,It.congr_env (by
     intro x hx
     simp only [show P384Joint.K.M.n=p384.n from rfl]
     exact (vt x hx).trans ((h.win.fields x hx).symm.trans (vs x hx).symm)),
    sps.trans (h.win.sp.trans spt.symm)⟩
 have vb : v<2^(64*P384Joint.K.M.n) := by
   rw [←h.win.left.scalar,show P384Joint.K.M.n=p384.n from rfl]
   exact wordsVal_lt ..
 have ub : u<2^(64*P384Joint.K.M.n) := by
   rw [←h.leftU,show P384Joint.K.M.n=p384.n from rfl]
   exact wordsVal_lt ..
 have zs':=zs
 have zt':=zt
 simp only [P384Joint.K,Cfg.winCfg,Cfg.pt] at zs' zt'
 rw [←show P384Joint.K.M.n=p384.n from rfl] at zs' zt'
 have genS : GeneratorInput p384.C base T (G p384.C) u _ :=
   ⟨h.sourceLeft.unch us (by decide) rs ws' (Exec.syms ps),gs,zs'⟩
 have genT : GeneratorInput p384.C base T (G p384.C) u _ :=
   ⟨h.sourceRight.unch ut (by decide) rt wt' (Exec.syms pt),gt,zt'⟩
 have one : toM p384.C.p (2^(64*P384Joint.K.M.n)) (p384.mont 1)=1 := by
   rw [show P384Joint.K.M.n=p384.n from rfl,toM_cmont hc.toBaseCfgOk]; rfl
 obtain ⟨hw,post⟩:=jointWindow_relCT (nafLayQ hc (by decide) (by decide))
   (unitMod_pow_two hc.p_odd (64*P384Joint.K.M.n)) hC hc.am3 (by simpa only [show P384Joint.K.M.n=p384.n from rfl] using hc.p_lt)
   (Nat.mod_lt _ (by have := hc.p_ge; omega)) one hwin (hD base) hct mixed hO hn17 hP hc.onG vb ub zs'
   _ _ _ _ _ _ ⟨pair,⟨ss,ms,Fs⟩,⟨st,mt,Ft⟩,genS,genT⟩ ws wt
 exact ⟨by rw [he,hw],post⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
