import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)

def packK (g : Nat) : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x0)] ∧ s.wr=[⟨s.gpr .x1,32*packWidth g⟩] ∧
    (polyRegion (s.gpr .x0)).Disjoint ⟨s.gpr .x1,32*packWidth g⟩ ∧ Reduced s.mem (s.gpr .x0)
  post s t := VG.Spec.Sha3.bytesAt t.mem (s.gpr .x1) (32*packWidth g)=highPacked g (polyAt s.mem (s.gpr .x0))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.sp=t.sp

/-- The public two-buffer precondition supplies every bounded load/store
permission required by the full packing function. -/
theorem contract_wp {g : Nat} (hg : IsG g) {s : State} (hp : (packK g).pre s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.HighPack.code g) s (CodePost g s) := by
  obtain ⟨hrd,hwr,hsep,hr⟩ := hp
  refine code_ok hg s hr hsep ?_ ?_ ?_
  · intro j hj k hk
    rw [hrd,Offset.add_add]
    exact ⟨polyRegion (s.gpr .x0),List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  · intro j hj
    rw [hwr]
    refine ⟨⟨s.gpr .x1,32*packWidth g⟩,List.mem_singleton_self _,Offset.contains_base _ ?_ ?_⟩
    · rcases hg with rfl | rfl
      · change 8*j+8≤128; omega
      · change 12*j+8≤192; omega
    · rcases hg with rfl | rfl
      · change 8*j<2^64; omega
      · change 12*j<2^64; omega
  · intro j hj hw
    rw [hwr,hw]
    change InRegions [⟨s.gpr .x1,192⟩]
      ((s.gpr .x1+BitVec.ofNat 64 (12*j))+BitVec.ofNat 64 8) 4
    rw [Offset.add_add]
    exact ⟨⟨s.gpr .x1,192⟩,List.mem_singleton_self _,Offset.contains_base _ (by omega) (by omega)⟩

/-- The measured function preserves the calling convention without stack
saves: its complete clobber set consists of caller-saved registers. -/
theorem pack_correct {g : Nat} (hg : IsG g) (s : State) (hp : (packK g).pre s) :
    ∃ trace t, Exec isa (Impl.MlDsa.AArch64.Optimized.HighPack.code g) s trace t ∧
      abiPreserved s t ∧ (packK g).post s t := by
  obtain ⟨trace,t,he,ht⟩ := contract_wp hg hp
  refine ⟨trace,t,he,⟨?_,ht.keep.sp,ht.keep.vcs⟩,ht.bytes⟩
  intro r hr
  apply ht.keep.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Only buffer addresses and stack pointer are public; coefficients remain secret. -/
theorem pack_ct {g : Nat} (hg : IsG g) :
    ConstantTime isa (packK g).pre (packK g).pub (Impl.MlDsa.AArch64.Optimized.HighPack.code g) := by
  have h : ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1]))
      (Impl.MlDsa.AArch64.Optimized.HighPack.code g) := by
    rcases hg with rfl | rfl
    · exact pack4_ct
    · exact pack6_ct
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply h s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  exact VG.Proof.MlKem.AArch64.agree_of hp.2.2 (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.1
    · exact hp.2.1)

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
