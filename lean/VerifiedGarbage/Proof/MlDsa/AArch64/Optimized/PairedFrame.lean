import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

/-- Internal paired phases may use saved SIMD registers before the outer
restore. This frame deliberately does not claim callee-saved preservation. -/
structure StepFrame (rs : List VReg) (s t : State) : Prop where
  gpr : t.gpr=s.gpr
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  vec : ∀r,r∉rs → t.v r=s.v r

theorem StepFrame.ofChg {rs : List VReg} {s t : State} (h : VChg rs s t) : StepFrame rs s t :=
  ⟨h.gpr,h.rd,h.wr,h.sp,h.v⟩
theorem StepFrame.ofMem {s t : State} {m : Mem} (h : VMem s t m) : StepFrame [] s t :=
  ⟨h.gpr,h.rd,h.wr,h.sp,fun _ _ => congrFun h.v _⟩
theorem StepFrame.trans {rs rt : List VReg} {s t u : State}
    (h : StepFrame rs s t) (h' : StepFrame rt t u) : StepFrame (rs++rt) s u :=
  ⟨h'.gpr.trans h.gpr,h'.rd.trans h.rd,h'.wr.trans h.wr,h'.sp.trans h.sp,fun r hr => by
    have hs : r∉rs := fun hm => hr (List.mem_append_left _ hm)
    have ht : r∉rt := fun hm => hr (List.mem_append_right _ hm)
    rw [h'.vec r ht,h.vec r hs]⟩
theorem StepFrame.mono {rs rt : List VReg} {s t : State} (h : StepFrame rs s t)
    (hm : ∀r∈rs,r∈rt) : StepFrame rt s t :=
  ⟨h.gpr,h.rd,h.wr,h.sp,fun r hr => h.vec r (fun hs => hr (hm r hs))⟩

theorem StepFrame.ofKeep {rs : List VReg} {s t : State} (h : Response.StepKeep rs s t) : StepFrame rs s t :=
  ⟨funext fun r => h.keep.get r (by simp), h.keep.rd, h.keep.wr, h.keep.sp,h.vec⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
