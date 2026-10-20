module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPairTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPairTiming
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.TCB.Axioms

/-! # Public completion flags and fixed-address restoration -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64

theorem restore_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19]))
    (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r,i)=>.ldr .x r .x19 (1800+8*i))) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x19]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem finish_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (ps : ProgressW w16 A B 3 p a b c s) (pu : ProgressW w16 A B 3 p a b c u)
    (ss : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) (us : u.syms "VG_MLKEM_REJ_SHUFFLE"=c)
    (fs : (s.gpr .x6).toNat=if (accepted A 3).length=256 ∧ (accepted B 3).length=256 then 1 else 0)
    (fu : (u.gpr .x6).toNat=if (accepted A 3).length=256 ∧ (accepted B 3).length=256 then 1 else 0)
    (sp : s.sp=u.sp) :
    RelCT isa (fun t v=>t=s ∧ v=u) (finishCode w16) (fun _ _=>True) := by
  have branch : RelCT isa (fun t v=>t=s ∧ v=u)
      (.ite (.zero .x .x6) (Impl.MlKem.AArch64.Paired.extraPair w16) (.block []))
      (fun t v=>t.sp=v.sp ∧ t.gpr .x19=v.gpr .x19) := by
    refine RelCT.ite ?_ ?_ (RelCT.block_nil ?_)
    · intro t v h
      rcases h with ⟨ht,hv⟩; subst t; subst v
      have hx := BitVec.eq_of_toNat_eq (fs.trans fu.symm)
      change some (s.gpr .x6==0)=some (u.gpr .x6==0)
      rw [hx]
    · intro t v tr ur t' v' h et ev
      rcases h.1 with ⟨ht,hv⟩; subst t; subst v
      have hh := extraPair_relCT ps pu ss us sp s u tr ur t' v' ⟨rfl,rfl⟩ et ev
      exact ⟨hh.1,hh.2.1.keep.sp.trans (sp.trans hh.2.2.keep.sp.symm),by
        rw [hh.2.1.keep.get .x19,hh.2.2.keep.get .x19,ps.ptr,pu.ptr]⟩
    · intro t v h
      rcases h.1 with ⟨ht,hv⟩; subst t; subst v
      exact ⟨sp,ps.ptr.trans pu.ptr.symm⟩
  refine RelCT.seq branch ?_
  intro t v tr ur t' v' h et ev
  exact ⟨restore_ct t v tr ur t' v' trivial trivial
    (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) et ev,trivial⟩

end VG.Proof.MlKem.AArch64.Paired
