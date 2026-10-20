module
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointDigitsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointStepTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

theorem jointWindow_relCT {C : Curve} {base T : Addr} {u v : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hpn : C.p<2^(64*P521Joint.K.M.n)) (hone_lt : P521Joint.K.one<C.p)
 (hone : toM C.p (2^(64*P521Joint.K.M.n)) P521Joint.K.one=1)
 (hc : WindowChecks P521Joint.K)
 (mixed : JacMixedChecks P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D)
 (hO : PrimeOrder C) (hn17 : 17≤C.n) {P G : Point C} (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hv : v<2^(64*P521Joint.K.M.n)) (hu : u<2^(64*P521Joint.K.M.n)) {E : Nat→Fe C}
 (hz1 : E P521Joint.K.P.z=1) :
 RelCT isa (fun s t=>FieldPair P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) (winRo P521Joint.K) E s t ∧
  (Scr s base 8192 ∧ ModOkA P521Joint.K.M 8192 C.p s.mem base ∧ NafFixed P521Joint.K C base s P v) ∧
  (Scr t base 8192 ∧ ModOkA P521Joint.K.M 8192 C.p t.mem base ∧ NafFixed P521Joint.K C base t P v) ∧
  GeneratorInput C base T G u s ∧ GeneratorInput C base T G u t)
 P521Joint.window (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  have hn0 := hL.win.n0
  intro s t ts tt s' t' ⟨pair, ⟨hs₁, hM₁, hF₁⟩, ⟨hs₂, hM₂, hF₂⟩,g₁,g₂⟩ es et
  rw [P521Joint.window] at es et
  cases es with | seq e1 es => cases es with | seq ec es => cases es with | seq e2 es =>
  cases es with | seq e3 es => cases es with | seq e4 e5 =>
  cases et with | seq f1 et => cases et with | seq fc et => cases et with | seq f2 et =>
  cases et with | seq f3 et => cases et with | seq f4 f5 =>
  -- The table.
  have hPz : P521Joint.K.P.z ∈ winRo P521Joint.K := by simp [winRo]
  obtain ⟨tr1, E1, p1⟩ := table_relCT hL hp hc.table _ _ _ _ _ _ pair e1 f1
  obtain ⟨_, _, x1, S1⟩ := table_ok hL hp hC hM3 hO hn17 hP hs₁ hM₁ hF₁
    ((pair.left.val _ hPz).trans hz1)
  obtain ⟨_, rfl⟩ := Exec.det e1 x1
  obtain ⟨_, _, y1, T1⟩ := table_ok hL hp hC hM3 hO hn17 hP hs₂ hM₂ hF₂
    ((pair.right.val _ hPz).trans hz1)
  obtain ⟨_, rfl⟩ := Exec.det f1 y1
  -- The cache, from which each run's loop goes on.
  have hsub : ∀ x ∈ winRo P521Joint.K ++ winTblSlots P521Joint.K, x ∈ tblLive P521Joint.K 8 := by
    intro x hx
    simp only [tblLive, winTblSlots, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inr hx
  have trc := (cache_relCT hL hp hc (P := P) _ _ _ _ _ _ ⟨p1.sub hsub, S1.tbl, T1.tbl⟩ ec fc).1
  have pc := (cache_relCT hL hp hc (P := P) _ _ _ _ _ _ ⟨p1.sub hsub, S1.tbl, T1.tbl⟩ ec fc).2
  have side : ∀ {a₀ a a' : State} {ta : List Leak}, Scr a₀ base 8192 → NafFixed P521Joint.K C base a₀ P v →
      NSt P521Joint.K C base 8192 P a₀ a → Exec isa (PubNaf.cache P521Joint.K) a ta a' →
      NafFixed P521Joint.K C base a' P v ∧ NSt P521Joint.K C base 8192 P a' a' ∧ CacheOk P521Joint.K C base a' ∧
        KeepRegs (nafClob P521Joint.K.M.n) a₀ a' ∧ Unch base (winW P521Joint.K ++ cacheW P521Joint.K) a₀.mem a'.mem := by
    intro a₀ a a' ta h₀ hF S ea
    obtain ⟨_, _, xa, sc, kc, Uc, Mc, Tc, Cc⟩ := cacheTo_ok hL hp S.scr S.mod S.tbl 8 (Nat.le_refl _)
    obtain ⟨_, rfl⟩ := Exec.det ea xa
    have U : Unch base (winW P521Joint.K ++ cacheW P521Joint.K) a₀.mem a'.mem := (S.unch.trans Uc).mono fun w hw => by
      simp only [List.mem_append] at hw ⊢
      rcases hw with hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
      · exact Or.inl (loopW_sub P521Joint.K w hw)
    exact ⟨hF.rebase hL U h₀.nowrap, ⟨sc, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, Mc, Tc⟩, Cc,
      S.keep.trans kc, U⟩
  obtain ⟨G₁, Sc1, Cc1, kc₁, uc₁⟩ := side hs₁ hF₁ S1 ec
  obtain ⟨G₂, Tc1, Cc2, kc₂, uc₂⟩ := side hs₂ hF₂ T1 fc
  have gen₁:=g₁.rebase uc₁ kc₁.rd kc₁.wr ((Exec.syms ec).trans (Exec.syms e1))
  have gen₂:=g₂.rebase uc₂ kc₂.rd kc₂.wr ((Exec.syms fc).trans (Exec.syms f1))
  -- `D = O` and the count.
  obtain ⟨tr2, ⟨E2, p2⟩, a19, b19⟩ := head_relCT hL hone_lt hc _ _ _ _ _ _ pc e2 f2
  obtain ⟨_, _, x2, S2, C2, _, Dl2, DJ2⟩ := head_ok hL hone_lt G₁ Sc1 Cc1 hv
  obtain ⟨_, rfl⟩ := Exec.det e2 x2
  obtain ⟨_, _, y2, T2, D2, _, Dl2', DJ2'⟩ := head_ok hL hone_lt G₂ Tc1 Cc2 hv
  obtain ⟨_, rfl⟩ := Exec.det f2 y2
  have top := jointPoint_topB (B:=64*P521Joint.K.M.n) (u:=u) (v:=v) G P hu hv
  change jointPoint G P u v 577=.infinity at top
  have hz:=Naf5.residual_zero_top hv
  change Naf5.residual v 577=0 at hz
  have dj {a : State} (h : InvJ C (tmv C P521Joint.K.M.n base a P521Joint.K.D.x)
    (tmv C P521Joint.K.M.n base a P521Joint.K.D.y) (tmv C P521Joint.K.M.n base a P521Joint.K.D.z)
    (mul (2*Naf5.residual v 577) P)) :
    InvJ C (tmv C P521Joint.K.M.n base a P521Joint.K.D.x)
    (tmv C P521Joint.K.M.n base a P521Joint.K.D.y) (tmv C P521Joint.K.M.n base a P521Joint.K.D.z)
    (add (jointPoint G P u v 577) (jointPoint G P u v 577)) := by
      rw [top]
      rw [hz,Nat.mul_zero,Spec.Weierstrass.mul] at h
      exact h
  obtain ⟨tr3, p3, I3, J3, sy3, ty3⟩:=jointDigits_relCT hL hp hC hM3 hone_lt hP hG
    (hC.onCurve_add (jointPoint_curve hC hG hP u v 577) (jointPoint_curve hC hG hP u v 577))
    G₁ G₂ gen₁ gen₂ hc.step.digit mixed (j:=576) (by decide)
    _ _ _ _ _ _ ⟨⟨E2,p2⟩,⟨S2,a19,Dl2,dj DJ2,C2⟩,⟨T2,b19,Dl2',dj DJ2',D2⟩,
      Exec.syms e2,Exec.syms f2⟩ e3 f3
  rw [jointPoint_step hC hG hP] at I3 J3
  obtain ⟨tr4, ⟨E4,p4⟩, I4, J4, _, _⟩:=jointLoop_relCT hL hp hC hM3 hone_lt hP hG
    G₁ G₂ gen₁ gen₂ hc.step mixed _ _ _ _ _ _ ⟨p3,I3,J3,sy3,ty3⟩ e4 f4
  -- Projective coordinates.
  have tr5 := hc.finish _ _ _ _ _ _ trivial trivial
    ⟨p4.sp, fun q hq => pub_x0 p4 (Taint.mem_ofRegs.mp hq)⟩ e5 f5
  obtain ⟨_, _, x5, S5, -, -⟩ := jointFinish_ok hL hp hC hpn hone_lt hone G₁ I4.st I4.rlt I4.r
  obtain ⟨_, rfl⟩ := Exec.det e5 x5
  obtain ⟨_, _, y5, T5, -, -⟩ := jointFinish_ok hL hp hC hpn hone_lt hone G₂ J4.st J4.rlt J4.r
  obtain ⟨_, rfl⟩ := Exec.det f5 y5
  refine ⟨by rw [tr1, trc, tr2, tr3, tr4, tr5], ?_, fun q hq => ?_⟩
  · exact (Exec.rdwr x5).2.2.trans (p4.sp.trans (Exec.rdwr y5).2.2.symm)
  · simp only [Taint.mem_ofRegs, List.mem_singleton] at hq
    subst hq
    exact S5.scr.x0.trans T5.scr.x0.symm

end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
