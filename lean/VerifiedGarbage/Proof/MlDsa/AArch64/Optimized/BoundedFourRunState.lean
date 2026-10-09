import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitialized
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeTwo

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.Sha3.AArch64.Neon

structure SamplerRun (σ s : State) (A : Nat→Spec.Sha3.State) (L : Nat→List Zq) : Prop where
 env : SamplerEnv σ s
 pair0 : PairAt s.mem (samplerScratch σ) (A 0) (A 1)
 pair1 : PairAt s.mem (samplerScratch σ+400#64) (A 2) (A 3)
 table : TableAt s.mem (samplerScratch σ+6000)
 fields : BatchFields s.mem (samplerScratch σ) (samplerOut σ) L

theorem Ready.running {σ s : State} (h : Ready σ s) : SamplerRun σ s (samplerA σ) (fun _=>[]) := by
  refine ⟨h.env,?_,?_,h.table,⟨by simp,by intro i hi j hj; simp at hj,?_⟩⟩
  · have hh:=h.pair 0 (by decide)
    change PairAt s.mem (samplerScratch σ+0#64) (samplerA σ 0) (samplerA σ 1) at hh
    rw [BitVec.add_zero] at hh
    exact hh
  · exact h.pair 1 (by decide)
  · intro i hi; exact h.counts i hi

theorem squeezeWrites_sub {b : Addr} {off : Nat} (ho : off≤272) {r : Region}
    (hr : r∈(squeezeCfg b off).writes) : Region.Sub r ⟨b,4096⟩ := by
  simp only [SqueezeCfg.writes,squeezeCfg,pairR,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact Region.sub_prefix (by decide)
  · exact Offset.sub_base b (d := 400) (n := 400) (k := 4096) (by decide)
  · exact Offset.sub_base b (d := 840+off) (n := 272) (k := 4096) (by omega)
  · exact Offset.sub_base b (d := 1384+off) (n := 272) (k := 4096) (by omega)
  · exact Offset.sub_base b (d := 1928+off) (n := 272) (k := 4096) (by omega)
  · exact Offset.sub_base b (d := 2472+off) (n := 272) (k := 4096) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
