import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem keep_sp {P : State → State → Prop} {c : Prog isa}
    (h : RelCT isa P c (fun _ _ => True)) (hp : ∀s t,P s t → s.sp=t.sp) :
    RelCT isa P c (fun s t => s.sp=t.sp) := by
  intro s t tr ur s' t' hab es et
  exact ⟨(h _ _ _ _ _ _ hab es et).1,(AArch64.Exec.sp es).trans ((hp _ _ hab).trans (AArch64.Exec.sp et).symm)⟩

theorem fourBody_relCT : RelCT isa FourPublic vectorBody (fun _ _ => True) := by
  unfold vectorBody
  apply RelCT.assoc
  apply RelCT.seq (keep_sp fourStep_relCT (fun _ _ h => h.2.2.2.2.2.1))
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)

theorem wideBody_relCT : RelCT isa WidePublic wideBody (fun _ _ => True) := by
  unfold wideBody
  apply RelCT.assoc
  apply RelCT.seq (keep_sp wideStep_relCT (fun _ _ h => h.2.2.2.2.2.1))
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
