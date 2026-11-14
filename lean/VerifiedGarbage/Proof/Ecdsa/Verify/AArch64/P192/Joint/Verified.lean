module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Timing
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Prefix
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Points
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.State
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Lit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Hash
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Hash
meta import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Spec.Ecdsa.P192
meta import VerifiedGarbage.Spec.Ecdsa.P192

/-! ### `Ecdsa.Verify.AArch64.P192.Joint.Public`, which only this module used -/

section

/-! Verification timing uses only inputs public in the existing ECDSA specification. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
open VG.Impl.Ecdsa.Verify.AArch64.P192.Joint

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
end VG.Proof.Ecdsa.Verify.AArch64.P192.Joint

end

end


/-! The joint verifier implements the unchanged public ECDSA contract. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192
open VG.Impl.Ecdsa.Verify.AArch64.P192.Joint

theorem public_of_spec {s t : State}
    (pub : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P192.inst AArch64.abi).pub s t) : Public s t := by
  sig_pub [Spec.Ecdsa.P192.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.P192.curve,Spec.Ecdsa.scratchWords,AArch64.abi,AArch64.argRegs] at pub
  obtain ⟨hsp,inputs,h0,h1,h2,h3⟩ := pub
  refine ⟨⟨hsp,fun r hr => ?_⟩,?_,?_⟩
  · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  all_goals
    have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append,Weierstrass.length_bytesAt])
    have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  · exact front.2
  · exact parts.2

theorem verify_a64 (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.AArch64.InvSounds) (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s',Exec isa verify s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := verify_ok (p192_ok hI) hL (pre_of hs)
  exact ⟨t,s',he,abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv,hpost⟩

theorem verify_verified (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target verify (Proof.Ecdsa.verifyContract Spec.Ecdsa.P192.inst AArch64.abi) := by
  refine ⟨?_,?_,implies.sat⟩
  · intro s hs
    obtain ⟨t,s',he,ha,hp⟩ := verify_a64 hL hI s (implies.pre s hs)
    exact ⟨t,s',he,ha,implies.post s s' hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact verify_ct (p192_ok hI) hL _ _ _ _ _ _
      (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (public_of_spec pub) e₁ e₂

/-- `P192.satState` satisfies the precondition of the verification of the `len` bytes. -/
theorem sat_spec : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P192.inst AArch64.abi).pre P192.satState := by
  sig_pre [Spec.Ecdsa.P192.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.P192.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, P192.satState]
  repeat' (first | exact Region.disjoint_of_sep (by decide) | decide | rfl | constructor)

/-- `vg_ecdsa_p192_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash
(`Hash.verifyHash_verified_nil`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target
      (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false verify)
      (Spec.Ecdsa.P192.inst.verifyHashContract AArch64.abi 80) :=
  Hash.verifyHash_verified_nil Proof.Ecdsa.Verify.p192_len (by decide) (verify_verified hL hI)
    (by taint_decide) (Hash.hashSat_nil (by decide) sat_spec (by decide) fun r hr => by
      simp only [P192.satState, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
