import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourAbsorb

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open ResidentRej (stateP scr)

def samplerInit : List Instr := Impl.MlDsa.AArch64.Sample.Rej4.pro++
 Impl.MlDsa.AArch64.Sample.Rej4.zeroStates++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.absorbPair 0++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.absorbPair 1

theorem pairs_disjoint (σ : State) : (pairR (stateP σ 0)).Disjoint (pairR (stateP σ 1)) :=
  Offset.disjoint (scr σ) (d := 400*0) (e := 400*1) (n := 400) (k := 400) (by decide) (by decide) (by decide)

theorem state_word (σ : State) (p i : Nat) : wordAddr (stateP σ p) i = wordAddr (scr σ) (25*p+i) := by
  change stateP σ p + BitVec.ofNat 64 (16*i) = scr σ + BitVec.ofNat 64 (16*(25*p+i))
  change (scr σ + BitVec.ofNat 64 (400*p)) + BitVec.ofNat 64 (16*i) = _
  rw [Offset.add_add,show 400*p+16*i = 16*(25*p+i) by omega]

/-- Absorb all four seeds as two pairs of lanes, preserving the ABI save record. -/
theorem initFour_ok {σ : State} (hp : SamplerPre σ) : WP isa (.block samplerInit) σ fun t => SamplerEnv σ t ∧
    PairAt t.mem (stateP σ 0) (samplerA σ 0) (samplerA σ 1) ∧
    PairAt t.mem (stateP σ 1) (samplerA σ 2) (samplerA σ 3) := by
  unfold samplerInit
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (samplerPro_ok hp) fun s1 he1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zeroAll_ok hp he1) fun s2 ⟨he2,hz2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (absorbPair_ok (p := 0) hp he2 (by decide : 2*0+1 < 4) (fun i hi => by
    rw [state_word,Nat.mul_zero,Nat.zero_add]; exact hz2 i (by omega))) fun s3 ⟨he3,hp3,hf3⟩ => ?_
  have hz3 : ∀ i < 25,s3.mem.read (wordAddr (stateP σ 1) i) 16 = 0 := by
    intro i hi
    rw [hf3.read (pair_contains (stateP σ 1) hi) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (pairs_disjoint σ).symm) (by decide),state_word]
    exact hz2 (25+i) (by omega)
  refine WP.mono (absorbPair_ok (p := 1) hp he3 (by decide : 2*1+1 < 4) hz3) fun t ⟨het,hpt,hft⟩ => ?_
  refine ⟨het,?_,hpt⟩
  intro i hi
  rw [hft.read (pair_contains (stateP σ 0) hi) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact pairs_disjoint σ) (by decide)]
  exact hp3 i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
