import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ProductBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

def inverseProductOps : List (VReg × Nat) :=
  (List.range 8).map fun j => (Inverse.vr j,16*j)

theorem inverseProduct_safe {j : Nat} (hj : j<8) :
    Inverse.vr j∉productTemps ∧ Inverse.vr j≠.v30 ∧ Inverse.vr j≠.v31 := by
  have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- All eight inputs are loaded before any inverse layer starts. Memory and
input pointers are unchanged, and each lane is the original exact product. -/
theorem inverseProductLoads_ok {s : State} (hc : ProductConstants s)
    (hr : ∀ j<8, InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (16*j)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (productClobs inverseProductOps) s t → ProductConstants t →
      (∀ j<8, ∀ e<4, vword (t.v (Inverse.vr j)) e=productInput s (16*j) e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (inverseProductLoads ++ rest)) s Q := by
  have hn : (inverseProductOps.map Prod.fst).Nodup := by decide
  have hd d off (hm : (d,off)∈inverseProductOps) :
      d∉productTemps ∧ d≠.v30 ∧ d≠.v31 := by
    obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
    cases h
    exact inverseProduct_safe (List.mem_range.mp hj)
  have hi d off (hm : (d,off)∈inverseProductOps) : off%16=0 ∧ off<4096*16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16 := by
    obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
    cases h
    have hj' := List.mem_range.mp hj
    exact ⟨by omega,by omega,hr j hj'⟩
  have eqcode : inverseProductOps.flatMap (fun p => productLoad p.1 p.2)=inverseProductLoads := by
    simp only [inverseProductOps,inverseProductLoads,List.flatMap_map]
  rw [← eqcode]
  refine productBatch_ok inverseProductOps hn hd hc hi fun t ht ct vt => k t ht ct ?_
  intro j hj e he
  exact vt _ _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩) e he

end VG.Proof.MlDsa.AArch64.Optimized
