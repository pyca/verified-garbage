module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.FrontRead
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Lit
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Loop

/-! Relate the shared loop's two executions at its public lookup boundary. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

private theorem front_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19])) stepFront :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

private theorem tail_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2])) digitTail :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem setup_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) setup :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

private theorem step_cut {s t : State} {tr : List Leak} (e : Exec isa step s tr t) :
    ∃ a tf tt, Exec isa stepFront s tf a ∧ Exec isa digitTail a tt t ∧ tr=tf++tt := by
  cases e with
  | seq ed e => cases e with
    | seq ea e => cases e with
      | seq eb e => cases e with
        | seq eg et =>
          exact ⟨_,_,_,.seq ed (.seq ea (.seq eb eg)),et,by simp only [List.append_assoc]⟩

/-- The peers may differ: only the public digit pair controls the lookup's trace. -/
theorem step_ct {base : Addr} {P Q₁ Q₂ : Point C} {u v j : Nat}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true)
    (hQ₁ : onCurve C Q₁=true) (hQ₂ : onCurve C Q₂=true) (h1 : 1 ≤ j) (h256 : j ≤ 128) :
    RelCT isa (fun s t => Running base P Q₁ u v j s ∧ Running base P Q₂ u v j t ∧ s.sp=t.sp)
      step (fun s t => Running base P Q₁ u v (j-1) s ∧ Running base P Q₂ u v (j-1) t ∧ s.sp=t.sp) := by
  intro s t ts tt s' t' ⟨hs,ht,sp⟩ es et
  obtain ⟨a,tf,ta,ef,ea,etr⟩ := step_cut es
  obtain ⟨b,tg,tb,eg,eb,ttr⟩ := step_cut et
  have hfg := front_ct _ _ _ _ _ _ trivial trivial ⟨sp,fun r hr => by
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.inputs.scr.x0.trans ht.inputs.scr.x0.symm
    · exact hs.counter.trans ht.counter.symm⟩ ef eg
  obtain ⟨_,_,ew,ha⟩ := stepFront_ok hc hC hP hQ₁ h1 h256 hs
  obtain ⟨_,rfl⟩ := Exec.det ef ew
  obtain ⟨_,_,ew,hb⟩ := stepFront_ok hc hC hP hQ₂ h1 h256 ht
  obtain ⟨_,rfl⟩ := Exec.det eg ew
  have hsp := (Exec.rdwr ef).2.2.trans (sp.trans (Exec.rdwr eg).2.2.symm)
  have hab := tail_ct _ _ _ _ _ _ trivial trivial ⟨hsp,fun r hr => by
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ha.1.x0.trans hb.1.x0.symm
    · exact ha.2.trans hb.2.symm⟩ ea eb
  obtain ⟨_,_,ew,_,hs'⟩ := step_ok hc hC hP hQ₁ h1 h256 hs
  obtain ⟨_,rfl⟩ := Exec.det es ew
  obtain ⟨_,_,ew,_,ht'⟩ := step_ok hc hC hP hQ₂ h1 h256 ht
  obtain ⟨_,rfl⟩ := Exec.det et ew
  exact ⟨by rw [etr,ttr,hfg,hab],hs',ht',(Exec.rdwr es).2.2.trans (sp.trans (Exec.rdwr et).2.2.symm)⟩

theorem loop_ct {base : Addr} {P Q₁ Q₂ : Point C} {u v : Nat}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true)
    (hQ₁ : onCurve C Q₁=true) (hQ₂ : onCurve C Q₂=true) :
    RelCT isa (fun s t => Running base P Q₁ u v 128 s ∧ Running base P Q₂ u v 128 t ∧ s.sp=t.sp)
      (.loop step (.nonzero .x .x19))
      (fun s t => Running base P Q₁ u v 0 s ∧ Running base P Q₂ u v 0 t ∧ s.sp=t.sp) := by
  let I := fun j s t => 1 ≤ j ∧ j ≤ 128 ∧
    Running base P Q₁ u v j s ∧ Running base P Q₂ u v j t ∧ s.sp=t.sp
  have H := RelCT.loop (M:=isa) (body:=step) (c:=.nonzero .x .x19)
    (Q:=fun s t => Running base P Q₁ u v 0 s ∧ Running base P Q₂ u v 0 t ∧ s.sp=t.sp) I (fun j => ?_) 128
  · exact H.mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)
  intro s t ts tt s' t' ⟨h1,h256,hs,ht,sp⟩ es et
  obtain ⟨eqtr,hs',ht',sp'⟩ := step_ct hc hC hP hQ₁ hQ₂ h1 h256 _ _ _ _ _ _ ⟨hs,ht,sp⟩ es et
  have heq : isa.eval (.nonzero .x .x19) s'=isa.eval (.nonzero .x .x19) t' := by
    change some (s'.read .x .x19 != 0)=some (t'.read .x .x19 != 0)
    rw [VG.Proof.Ed25519.AArch64.read_x,VG.Proof.Ed25519.AArch64.read_x,hs'.counter,ht'.counter]
  have ev : isa.eval (.nonzero .x .x19) s'=some (decide (j-1 ≠ 0)) := by
    change some (s'.read .x .x19 != 0)=_
    rw [VG.Proof.Ed25519.AArch64.read_x,hs'.counter]
    congr 1
    by_cases hz : j-1=0
    · rw [hz]; rfl
    · rw [decide_eq_true hz,bne_iff_ne,ne_eq]
      intro hh
      have hn := congrArg BitVec.toNat hh
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hn
      exact hz hn
  refine ⟨eqtr,heq,?_,?_⟩
  · intro hz
    rw [ev,Option.some.injEq,decide_eq_false_iff_not,ne_eq,not_not] at hz
    rw [hz] at hs' ht'
    exact ⟨hs',ht',sp'⟩
  · intro hn
    rw [ev,Option.some.injEq,decide_eq_true_eq] at hn
    exact ⟨j-1,by omega,by omega,by omega,hs',ht',sp'⟩
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
