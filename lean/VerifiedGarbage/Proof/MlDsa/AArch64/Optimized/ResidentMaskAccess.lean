import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskSponge

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

theorem pairAccess_ok {σ s : State} {d : Nat} (hp : Pre σ) (he : Env σ s)
    (hd : d=18 ∨ d=20) : PairAccess d s := by
  have hr (off len : Nat) (hb : off+len≤8192) :
      InRegions (s.rd++s.wr) (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.rd,he.wr]
    exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ hb (by omega)⟩
  have hs : ∀ p∈[Reg.x21,.x22],
      (Region.mk (σ.gpr .x4) 8192).Disjoint ⟨s.gpr p,1024⟩ := by
    intro p hp'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [he.out1]; exact hp.out1Sep.symm
    · rw [he.out2]; exact hp.out2Sep.symm
  have hw : ∀ p∈[Reg.x21,.x22], (Region.mk (s.gpr p) 1024)∈s.wr := by
    intro p hp'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [he.out1,he.wr]; exact hp.out1
    · rw [he.out2,he.wr]; exact hp.out2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro off hoff j hj
    rw [he.base,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro off hoff j hj
    rw [he.base,Offset.add_add,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro off hoff j hj
    rw [he.base,Offset.add_add,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro p hp' j hj g hg
    rw [Offset.add_add]
    exact ⟨_,hw p hp',Offset.contains_base _ (by omega) (by omega)⟩
  · intro off hoff p hp'
    rw [he.base]
    refine (hs p hp').sub_left (Offset.sub_base _ ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · rw [he.out1,he.out2]; exact hp.outputs

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
