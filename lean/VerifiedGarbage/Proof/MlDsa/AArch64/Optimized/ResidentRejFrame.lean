import VerifiedGarbage.Proof.MlKem.AArch64.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

/-- Register-only matrix-parser fragments carry both GPR and vector frames. -/
structure ProbeFrame (gs : List Reg) (vs : List VReg) (s t : State) : Prop where
  only : Only gs s t
  vectors : ∀r,r∉vs → t.v r=s.v r

namespace ProbeFrame

theorem trans {gs gs' vs vs'} {s t u : State}
    (h : ProbeFrame gs vs s t) (h' : ProbeFrame gs' vs' t u) :
    ProbeFrame (gs++gs') (vs++vs') s u :=
  ⟨h.only.trans h'.only,fun r hr => (h'.vectors r (fun hm => hr (List.mem_append_right _ hm))).trans
    (h.vectors r (fun hm => hr (List.mem_append_left _ hm)))⟩

theorem mono {gs gs' vs vs'} {s t : State} (h : ProbeFrame gs vs s t)
    (hg : ∀r∈gs,r∈gs') (hv : ∀r∈vs,r∈vs') : ProbeFrame gs' vs' s t :=
  ⟨h.only.mono hg,fun r hr => h.vectors r (fun hm => hr (hv r hm))⟩

theorem ofVector {vs : List VReg} {s t : State} (h : VChg vs s t)
    (hv : ∀r∈preservedV,r∉vs) : ProbeFrame [] vs s t :=
  ⟨⟨fun _ _ => by rw [h.gpr],h.mem,h.rd,h.wr,h.sp,
    fun r hr => by rw [h.v r (hv r hr)]⟩,h.v⟩

theorem ofScalar {gs : List Reg} {s t : State} (h : Only gs s t)
    (hv : t.v=s.v) : ProbeFrame gs [] s t := ⟨h,fun _ _ => congrFun hv _⟩

end ProbeFrame
end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
