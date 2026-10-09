import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBank

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

/-- All eight inputs are loaded before any inverse layer starts. Memory and
input pointers are unchanged, and each lane is the original exact product. -/
theorem inverseDotLoads_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) {s : State} (hc : ProductConstants s)
    (hr : ∀ j<8,∀ k<n, InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+16*j)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+16*j)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg (productClobs inverseProductOps) s t → ProductConstants t →
      (∀ j<8, ∀ e<4, vword (t.v (Inverse.vr j)) e=dotResult s n (16*j) e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (inverseDotLoads n ++ rest)) s Q := by
  have hnDistinct : (inverseProductOps.map Prod.fst).Nodup := by decide
  have hd d off (hm : (d,off)∈inverseProductOps) :
      d∉productTemps ∧ d≠.v30 ∧ d≠.v31 := by
    obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
    cases h
    exact inverseProduct_safe (List.mem_range.mp hj)
  have hi d off (hm : (d,off)∈inverseProductOps) : ∀ k<n,
      (1024*k+off)%16=0 ∧ 1024*k+off<4096*16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16 := by
    obtain ⟨j,hj,h⟩ := List.mem_map.mp hm
    cases h
    have hj' := List.mem_range.mp hj
    intro k hk
    refine ⟨?_,by omega,hr j hj' k hk⟩
    omega
  have eqcode : inverseProductOps.flatMap (fun p => dotLoad n p.1 p.2)=inverseDotLoads n := by
    simp only [inverseProductOps,inverseDotLoads,List.flatMap_map]
  rw [← eqcode]
  refine dotBatch_ok hn inverseProductOps hnDistinct hd hc hi fun t ht ct vt => k t ht ct ?_
  intro j hj e he
  exact vt _ _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩) e he

end VG.Proof.MlDsa.AArch64.Optimized
