import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg VMem)

/-- SIMD arithmetic with intervening stores keeps the scalar call frame. -/
structure StepKeep (rs : List VReg) (s t : State) : Prop where
  keep : Keep [] s t
  vec : ∀r,r∉rs → t.v r=s.v r

theorem StepKeep.ofChg {rs : List VReg} {s t : State} (h : VChg rs s t)
    (hv : ∀r∈preservedV,r∉rs) : StepKeep rs s t := ⟨h.keep hv,h.v⟩
theorem StepKeep.ofMem {s t : State} {m : Mem} (h : VMem s t m) : StepKeep [] s t :=
  ⟨h.keep,fun _ _ => congrFun h.v _⟩
theorem StepKeep.trans {rs rt : List VReg} {s t u : State}
    (h : StepKeep rs s t) (h' : StepKeep rt t u) : StepKeep (rs++rt) s u :=
  ⟨(h.keep.trans h'.keep).mono,fun r hr => by
    have hs : r∉rs := fun hm => hr (List.mem_append_left _ hm)
    have ht : r∉rt := fun hm => hr (List.mem_append_right _ hm)
    rw [h'.vec r ht,h.vec r hs]⟩
theorem StepKeep.mono {rs rt : List VReg} {s t : State} (h : StepKeep rs s t)
    (hm : ∀r∈rs,r∈rt) : StepKeep rt s t :=
  ⟨h.keep,fun r hr => h.vec r (fun hs => hr (hm r hs))⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response
