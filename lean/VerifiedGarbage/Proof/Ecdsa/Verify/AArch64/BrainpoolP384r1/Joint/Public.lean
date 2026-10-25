module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Timing
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Prefix
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Points
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.State
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front

/-! Verification timing uses only inputs public in the existing ECDSA specification. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

/-- No point coordinates or table contents need to agree between runs. -/
theorem points_ct {base : Addr} {s₁ s₂ a b : State} {g₁ g₂ : Reg → BitVec 64}
    (hc : BaseCfgOk cfg) (hC : Law C)
    (hm₁ : Mid cfg s₁ base g₁ a) (hm₂ : Mid cfg s₂ base g₂ b)
    (hu : sv cfg base a U=sv cfg base b U) (hv : sv cfg base a V=sv cfg base b V)
    (sp : a.sp=b.sp) {ta tb : List Leak} {a' b' : State}
    (ea : Exec isa points a ta a') (eb : Exec isa points b tb b') :
    ta=tb ∧ a'.gpr .x0=b'.gpr .x0 ∧ a'.sp=b'.sp := by
  let P := peerPt cfg (s₁.mem (s₁.gpr .x0)=4) (keyX cfg s₁) (keyY cfg s₁)
  let Q := peerPt cfg (s₂.mem (s₂.gpr .x0)=4) (keyX cfg s₂) (keyY cfg s₂)
  have hP : onCurve C P=true := peerPt_onCurve hc _ _ _
  have hQ : onCurve C Q=true := peerPt_onCurve hc _ _ _
  have rep₁ : Rep C (val base a qSource.x) (val base a qSource.y) (val base a qSource.z) P := by
    rw [show val base a qSource.z=1 from onep_tmv hc hm₁.fixed]
    exact peerPt_rep hC _ _ _ hm₁.px hm₁.py
  have rep₂ : Rep C (val base b qSource.x) (val base b qSource.y) (val base b qSource.z) Q := by
    rw [show val base b qSource.z=1 from onep_tmv hc hm₂.fixed]
    exact peerPt_rep hC _ _ _ hm₂.px hm₂.py
  cases ea with
  | seq epa ela => cases eb with
    | seq epb elb =>
      have et := setup_ct _ _ _ _ _ _ trivial trivial ⟨sp,fun r hr => by
        simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
        subst hr
        exact hm₁.scr.x0.trans hm₂.scr.x0.symm⟩ epa epb
      obtain ⟨_,_,w₁,_,run₁⟩ := setup_ok hc hC hP hm₁ rep₁
      obtain ⟨_,rfl⟩ := Exec.det epa w₁
      obtain ⟨_,_,w₂,_,run₂⟩ := setup_ok hc hC hQ hm₂ rep₂
      obtain ⟨_,rfl⟩ := Exec.det epb w₂
      rw [←hu,←hv] at run₂
      have sp' := (Exec.rdwr epa).2.2.trans (sp.trans (Exec.rdwr epb).2.2.symm)
      obtain ⟨eqloop,r₁,r₂,_⟩ := loop_ct hc hC hc.onG hP hQ _ _ _ _ _ _ ⟨run₁,run₂,sp'⟩ ela elb
      exact ⟨by rw [et,eqloop],r₁.inputs.scr.x0.trans r₂.inputs.scr.x0.symm,
        (Exec.rdwr ela).2.2.trans (sp'.trans (Exec.rdwr elb).2.2.symm)⟩

structure Public (s t : State) : Prop where
  ptrs : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3]) s t
  digest : Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) cfg.C.len =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x1) cfg.C.len
  sig : Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (2*cfg.C.len) =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x2) (2*cfg.C.len)

theorem Public.scalars {s t : State} (h : Public s t) :
    publicU cfg s=publicU cfg t ∧ publicV cfg s=publicV cfg t := by
  refine ⟨publicU_congr h.digest h.sig,?_⟩
  have hs := h.sig
  rw [Nat.two_mul,bytesAt_add,bytesAt_add] at hs
  obtain ⟨hr,hs⟩ := List.append_inj hs (by simp only [length_bytesAt])
  have hr' : sigR cfg s=sigR cfg t := congrArg Spec.Weierstrass.ofBytes hr
  have hs' : sigS cfg s=sigS cfg t := congrArg Spec.Weierstrass.ofBytes hs
  rw [publicV,publicV,hr',hs']

theorem verify_ct (hc : BaseCfgOk cfg) (hC : Law C) :
    ConstantTime isa (FrontPre cfg) Public verify := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  obtain ⟨a₁,b₁,tp₁,tc₁,ts₁,ep₁,ec₁,es₁,et₁⟩ := verify_cut e₁
  obtain ⟨a₂,b₂,tp₂,tc₂,ts₂,ep₂,ec₂,es₂,et₂⟩ := verify_cut e₂
  have ht := prefix_ct _ _ _ _ _ _ trivial trivial pub.ptrs ep₁ ep₂
  obtain ⟨_,_,wp₁,g₁,hm₁⟩ := prefix_ok hc pre₁
  obtain ⟨_,rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_,_,wp₂,g₂,hm₂⟩ := prefix_ok hc pre₂
  obtain ⟨_,rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3=s₂.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  rw [←base] at hm₂
  have hu : sv cfg (s₁.gpr .x3) a₁ U=sv cfg (s₁.gpr .x3) a₂ U :=
    (mid_publicU hm₁).trans (pub.scalars.1.trans (mid_publicU hm₂).symm)
  have hv : sv cfg (s₁.gpr .x3) a₁ V=sv cfg (s₁.gpr .x3) a₂ V :=
    (mid_publicV hm₁).trans (pub.scalars.2.trans (mid_publicV hm₂).symm)
  have sp := (Exec.rdwr ep₁).2.2.trans (pub.ptrs.1.trans (Exec.rdwr ep₂).2.2.symm)
  obtain ⟨hm,h0,hsp⟩ := points_ct hc hC hm₁ hm₂ hu hv sp ec₁ ec₂
  have hs := suffix_ct _ _ _ _ _ _ trivial trivial ⟨hsp,fun r hr => by
    simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
    subst hr
    exact h0⟩ es₁ es₂
  rw [et₁,et₂,ht,hm,hs]
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
