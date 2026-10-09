import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintSpecPre

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem pairedCoeff_frame {rs : List Region} {m m' : Mem} {p : Addr}
    (hf : Frame rs m m') (hd : ∀r∈rs,(⟨p,2048⟩:Region).Disjoint r)
    {j k : Nat} (hj : j<2) (hk : k<n) :
    coeffAt m' (pairPolyPtr p j) k=coeffAt m (pairPolyPtr p j) k := by
  apply VG.Proof.MlDsa.Verify.coeffAt_congr _ hk
  apply VG.Proof.MlKem.bytes_frame hf _ (by decide)
  intro r hr
  exact (hd r hr).sub_left (Offset.sub_base _ (by omega))

theorem pairedHintBase_frame {rs : List Region} {m m' : Mem} {out aux : Addr}
    (hf : Frame rs m m') (ho : ∀r∈rs,(⟨out,2048⟩:Region).Disjoint r)
    (ha : ∀r∈rs,(⟨aux,2048⟩:Region).Disjoint r) (g : Nat)
    {j k : Nat} (hj : j<2) (hk : k<n) :
    responseHintBase m' (pairPolyPtr out j) (pairPolyPtr aux j) g k=
      responseHintBase m (pairPolyPtr out j) (pairPolyPtr aux j) g k := by
  rw [responseHintBase,pairedCoeff_frame hf ho hj hk,pairedCoeff_frame hf ha hj hk]
  rfl

structure HintEntryFrame (s : State) (m : Mem) : Prop where
  products : pairedProductsReduced m (s.gpr .x0) (s.gpr .x1)
  decomposed : ∀j<2,ResponseDecomposed m (pairPolyPtr (s.gpr .x2) j)
    (pairPolyPtr (s.gpr .x3) j) ((s.gpr .x5).setWidth 32).toNat
  product : ∀j<2,pairedProduct m (s.gpr .x0) (s.gpr .x1) j=pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j
  hints : ∀j<2,pairedHintPoly m (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) ((s.gpr .x5).setWidth 32).toNat j=
    pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) ((s.gpr .x5).setWidth 32).toNat j

theorem hintEntry_frame {s : State} {m : Mem} (h : HintSpecPre s)
    (hf : Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem m) : HintEntryFrame s m := by
  have sep {p : Addr} {len : Nat} (hd : (⟨p,len⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩) :
      ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨p,len⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hd.sub_right (Offset.sub_base _ (by decide))
  have hc := sep h.commonWork
  have hs := sep h.secretWork
  have ho := sep h.dataWork
  have ha := sep h.auxWork
  refine ⟨pairedProductsReduced_frame hf hc hs h.products,?_,fun j hj => pairedProduct_frame hf hc hs hj,?_⟩
  · intro j hj k hk
    rw [pairedCoeff_frame hf ho hj hk,pairedCoeff_frame hf ha hj hk,pairedHintBase_frame hf ho ha _ hj hk]
    exact h.decomposed j hj k hk
  · intro j hj
    apply Vector.ext
    intro k hk
    simp only [pairedHintPoly,Vector.getElem_ofFn]
    rw [pairedProduct_frame hf hc hs hj,pairedHintBase_frame hf ho ha _ hj hk]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
