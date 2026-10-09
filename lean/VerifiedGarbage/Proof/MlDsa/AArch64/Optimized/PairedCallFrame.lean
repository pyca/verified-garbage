import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure CallFrame (gr : List Reg) (vr : List VReg) (s t : State) : Prop where
  gpr : ∀r,r∉gr → t.gpr r=s.gpr r
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  vec : ∀r,r∉vr → t.v r=s.v r

theorem CallFrame.ofStep {vr : List VReg} {s t : State} (h : StepFrame vr s t) : CallFrame [] vr s t :=
  ⟨fun _ _ => congrFun h.gpr _,h.rd,h.wr,h.sp,h.vec⟩
theorem CallFrame.ofKeep {gr : List Reg} {s t : State} (h : Keep gr s t) (hv : t.v=s.v) : CallFrame gr [] s t :=
  ⟨fun r hr => h.get r hr,h.rd,h.wr,h.sp,fun _ _ => congrFun hv _⟩
theorem CallFrame.trans {gr gs : List Reg} {vr vs : List VReg} {s t u : State}
    (h : CallFrame gr vr s t) (h' : CallFrame gs vs t u) : CallFrame (gr++gs) (vr++vs) s u := by
  refine ⟨?_,h'.rd.trans h.rd,h'.wr.trans h.wr,h'.sp.trans h.sp,?_⟩
  · intro r hr
    rw [h'.gpr r (fun hm => hr (List.mem_append_right _ hm)),h.gpr r (fun hm => hr (List.mem_append_left _ hm))]
  · intro r hr
    rw [h'.vec r (fun hm => hr (List.mem_append_right _ hm)),h.vec r (fun hm => hr (List.mem_append_left _ hm))]
theorem CallFrame.mono {gr gs : List Reg} {vr vs : List VReg} {s t : State}
    (h : CallFrame gr vr s t) (hg : gr⊆gs) (hv : vr⊆vs) : CallFrame gs vs s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (hg hm)),h.rd,h.wr,h.sp,
    fun r hr => h.vec r (fun hm => hr (hv hm))⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
