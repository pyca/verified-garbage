import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

def outputAt (p : Addr) (i : Nat) : Addr := p+BitVec.ofNat 64 (1024*i)
def countAt (b : Addr) (i : Nat) : Addr := b+BitVec.ofNat 64 (7904+8*i)
def inputAt (b : Addr) (i off : Nat) : Addr := b+BitVec.ofNat 64 (840+544*i+off)
def batchWrites (b p : Addr) : List Region := [⟨p,4096⟩,⟨b+7904,32⟩]

theorem outputAt_sub (p : Addr) {i : Nat} (hi : i<4) :
    Region.Sub (polyR (outputAt p i)) ⟨p,4096⟩ := Offset.sub_base p (by omega)

theorem countAt_sub (b : Addr) {i : Nat} (hi : i<4) :
    Region.Sub ⟨countAt b i,8⟩ ⟨b+7904,32⟩ := by
  have he : countAt b i=b+7904#64+BitVec.ofNat 64 (8*i) := by
    simp only [countAt,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [he]
  exact Offset.sub_base _ (by omega)

theorem outputs_apart (p : Addr) {i j : Nat} (hi : i<4) (hj : j<4) (hne : i≠j) :
    (polyR (outputAt p i)).Disjoint (polyR (outputAt p j)) :=
  Offset.disjoint p (by omega) (by omega) (by omega)

theorem counts_apart (b : Addr) {i j : Nat} (hi : i<4) (hj : j<4) (hne : i≠j) :
    (⟨countAt b i,8⟩ : Region).Disjoint ⟨countAt b j,8⟩ :=
  Offset.disjoint b (by omega) (by omega) (by omega)

theorem parseFrame_batch {b p : Addr} {i : Nat} (hi : i<4) {m m' : Mem}
    (hf : Frame [polyR (outputAt p i),⟨countAt b i,8⟩] m m') :
    Frame (batchWrites b p) m m' := by
  refine hf.sub ?_
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨⟨p,4096⟩,by simp [batchWrites],outputAt_sub p hi⟩
  · exact ⟨⟨b+7904,32⟩,by simp [batchWrites],countAt_sub b hi⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
