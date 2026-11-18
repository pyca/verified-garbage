module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejFour
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejFour
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! ### `MlDsa.AArch64.Optimized.ResidentRejFixedTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Impl.MlDsa.AArch64.Sample

abbrev PointerCT (rs : List Reg) (c : Prog isa) :=
  ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs rs)) c

theorem startFour_ct : PointerCT [.x0,.x1,.x2] (.block (Rej4.init++Four.initCounts)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem startTwo_ct : PointerCT [.x0,.x1,.x2]
    (.block (Rej4.pro++Rej4.zeroStates++Rej4.absorbPair 0++Two.initCounts)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem flagsFour_ct : PointerCT [.x19] (.block Four.flags) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem flagsTwo_ct : PointerCT [.x19] (.block Two.flags) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem sixthFour_ct : PointerCT [.x19] (Four.squeezeN step 840 1) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem sixthTwo_ct : PointerCT [.x19] (Two.squeezeN Two.step 840 1) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem firstTwo_ct : PointerCT [.x19]
    (.seq (.block (Two.squeezeSetup 0 5)) (five .x22 .x24 .x25)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

 theorem env_relCT {v : Nat} {σ τ : State} {P Q R S : State → Prop} {c : Prog isa}
    (pub : Pub v σ τ) (hs : ∀s,P s → Env v σ s) (ht : ∀s,Q s → Env v τ s)
    (hc : PointerCT [.x19] c) (ws : ∀s,P s → WP isa c s R)
    (wt : ∀t,Q t → WP isa c t S) :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => R s ∧ S t) := by
  have ct : RelCT isa (fun s t => P s ∧ Q t) c (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have se := hs s h.1
    have te := ht t h.2
    have ha : VG.AArch64.Taint.Agree (Taint.ofRegs [.x19]) s t := by
      refine ⟨se.sp.trans (pub.2.2.2.1.trans te.sp.symm),?_⟩
      simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton]
      intro r hr
      subst r
      rw [se.x19,te.x19,pub.2.2.1]
    exact ⟨hc s t tr ur s' t' True.intro True.intro ha es et,True.intro⟩
  exact (ct.wp (fun s t h => ⟨ws s h.1,wt t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
