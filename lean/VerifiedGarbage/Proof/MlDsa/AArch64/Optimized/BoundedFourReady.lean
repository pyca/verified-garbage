import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCounts
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitVerified

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open ResidentRej (stateP scr lowR)

structure InitialPairs (σ s : State) : Prop where
 env : SamplerEnv σ s
 pair : ∀p<2,PairAt s.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1))

structure Ready (σ s : State) : Prop extends InitialPairs σ s where
 counts : ∀i<4,s.mem.readW (countAt (scr σ) i) 64=256
 table : TableAt s.mem (scr σ+6000)

theorem pairs_count_keep {σ s t : State} (hs : InitialPairs σ s)
    (hf : Frame [⟨scr σ+7904#64,32⟩] s.mem t.mem) {p : Nat} (hp : p<2) :
    PairAt t.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1)) := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ p) hi) (fun r hr=>by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint (scr σ) (d := 400*p) (e := 7904) (n := 400) (k := 32)
      (by omega) (by omega) (by decide)) (by decide)]
  exact hs.pair p hp i hi

theorem initCounts_pairs {σ s : State} (hp : SamplerPre σ) (hs : InitialPairs σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts) s fun t=>
      InitialPairs σ t ∧∀i<4,t.mem.readW (countAt (scr σ) i) 64=256 := by
  refine WP.mono (initCounts_ok hs.env.x19 (fun i hi=>sampler_in_work hp hs.env.wr (by omega)))
    fun t ⟨⟨ht,hf,hc⟩,_⟩=>?_
  refine ⟨⟨?_,fun p hp=>pairs_count_keep hs hf hp⟩,hc⟩
  exact hs.env.lowStep hf (fun r hr=>by
    rw [List.mem_singleton.mp hr]
    exact Offset.sub_base (scr σ) (d := 7904) (n := 32) (k := 7968) (by decide))
    ht.rd ht.wr ht.sp (fun r hr=>ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;> decide))

theorem tableInit_ready {σ s : State} (hp : SamplerPre σ) (hs : InitialPairs σ s)
    (hc : ∀i<4,s.mem.readW (countAt (scr σ) i) 64=256) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.BoundedFour.tableInit true)) s (Ready σ) := by
  rw [←List.append_nil (Impl.MlDsa.AArch64.Optimized.BoundedFour.tableInit true)]
  refine tableInit_ok (fun a n h=>?_) fun t ht hv htable hf=>WP.block_nil_iff.mpr ?_
  · obtain ⟨r,hr,hcontains⟩:=h
    rw [List.mem_singleton.mp hr] at hcontains
    rw [hs.env.x19] at hcontains
    rw [hs.env.wr,hp.wr]
    exact ⟨samplerWorkspace σ,by simp,by
      change (a-scr σ).toNat+n≤8192
      change (a-(scr σ+6000#64)).toNat+n≤1024 at hcontains
      have hadd : a-scr σ=(a-(scr σ+6000#64))+6000#64 := by bv_omega
      rw [hadd]
      rw [BitVec.toNat_add,show (6000#64).toNat=6000 from rfl]
      have hh:=Nat.mod_le ((a-(scr σ+6000#64)).toNat+6000) (2^64)
      omega⟩
  · rw [hs.env.x19] at hf htable
    refine ⟨⟨?_,?_⟩,?_,htable⟩
    · exact hs.env.lowStep hf (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.sub_base (scr σ) (d := 6000) (n := 1024) (k := 7968) (by decide))
        ht.rd ht.wr ht.sp (fun r hr=>ht.get r (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl|rfl <;> decide))
    · intro p hp i hi
      rw [hf.read (pair_contains (stateP σ p) hi) (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (scr σ) (d := 400*p) (e := 6000) (n := 400) (k := 1024)
          (by omega) (by omega) (by decide)) (by decide)]
      exact hs.pair p hp i hi
    · intro i hi
      rw [hf.readW (Region.contains_self (countAt (scr σ) i) 8) (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (scr σ) (d := 7904+8*i) (e := 6000) (n := 8) (k := 1024)
          (by omega) (by omega) (by decide)) (by decide)]
      exact hc i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
