import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejCounts

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (init)

theorem pairs_disjoint (σ : State) : (pairR (stateP σ 0)).Disjoint (pairR (stateP σ 1)) :=
  Offset.disjoint (scr σ) (d := 400*0) (e := 400*1) (n := 400) (k := 400) (by decide) (by decide) (by decide)

theorem state_word (σ : State) (p i : Nat) : wordAddr (stateP σ p) i = wordAddr (scr σ) (25*p+i) := by
  change stateP σ p + BitVec.ofNat 64 (16*i) = scr σ + BitVec.ofNat 64 (16*(25*p+i))
  change (scr σ + BitVec.ofNat 64 (400*p)) + BitVec.ofNat 64 (16*i) = _
  rw [Offset.add_add,show 400*p+16*i = 16*(25*p+i) by omega]

/-- Absorb all four seeds as two pairs of lanes, preserving the ABI save record. -/
theorem initFour_ok {σ : State} (hp : Pre 4 σ) : WP isa (.block init) σ fun t => Env 4 σ t ∧
    PairAt t.mem (stateP σ 0) (A0 σ 0) (A0 σ 1) ∧
    PairAt t.mem (stateP σ 1) (A0 σ 2) (A0 σ 3) := by
  unfold init
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_ok hp) fun s1 he1 => ?_
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
/-- The two-stream entry reads precisely two 34-byte seeds. -/
theorem initTwo_ok {σ : State} (hp : Pre 2 σ) :
    WP isa (.block (Impl.MlDsa.AArch64.Sample.Rej4.pro ++
      Impl.MlDsa.AArch64.Sample.Rej4.zeroStates ++
      Impl.MlDsa.AArch64.Sample.Rej4.absorbPair 0)) σ fun t =>
      Env 2 σ t ∧ PairAt t.mem (stateP σ 0) (A0 σ 0) (A0 σ 1) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_ok hp) fun s1 he1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zeroAll_ok hp he1) fun s2 ⟨he2,hz2⟩ => ?_
  refine WP.mono (absorbPair_ok (p := 0) hp he2 (by decide) (fun i hi => by
    rw [state_word,Nat.mul_zero,Nat.zero_add]; exact hz2 i (by omega)))
    fun _ ⟨he,hp,_⟩ => ⟨he,hp⟩

theorem pair_count_disjoint (σ : State) {p : Nat} (hp : p<2) :
    (pairR (stateP σ p)).Disjoint (countR σ) :=
  Offset.disjoint (scr σ) (d := 400*p) (e := 7904) (n := 400) (k := 32)
    (by omega) (by omega) (by decide)

theorem initCounts_pair {v : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s)
    (hpair : ∀p,2*p+1<v → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1))) :
    WP isa (.block (initCountsCode v)) s fun t => Env v σ t ∧
      (∀p,2*p+1<v → PairAt t.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1))) ∧
      ∀i<v,t.mem.readW (countP σ i) 64=256 := by
  refine WP.mono (initCounts_ok hp he) fun t ⟨het,hf,hc⟩ => ⟨het,?_,hc⟩
  intro p hpn i hi
  rw [hf.read (pair_contains (stateP σ p) hi) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact pair_count_disjoint σ (by have:=hp.streams; omega)) (by decide)]
  exact hpair p hpn i hi

theorem startFour_ok {σ : State} (hp : Pre 4 σ) :
    WP isa (.block (Impl.MlDsa.AArch64.Sample.Rej4.init ++
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.initCounts)) σ fun t =>
      Env 4 σ t ∧
      (∀p,2*p+1<4 → PairAt t.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1))) ∧
      ∀i<4,t.mem.readW (countP σ i) 64=256 := by
  rw [WP.block_append_iff]
  refine WP.mono (initFour_ok hp) fun s ⟨he,h0,h1⟩ => ?_
  exact initCounts_pair hp he (fun p h => by
    rcases (show p=0 ∨ p=1 by omega) with rfl | rfl
    · exact h0
    · exact h1)

theorem startTwo_ok {σ : State} (hp : Pre 2 σ) :
    WP isa (.block (Impl.MlDsa.AArch64.Sample.Rej4.pro ++
      Impl.MlDsa.AArch64.Sample.Rej4.zeroStates ++
      Impl.MlDsa.AArch64.Sample.Rej4.absorbPair 0 ++
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.initCounts)) σ fun t =>
      Env 2 σ t ∧
      (∀p,2*p+1<2 → PairAt t.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1))) ∧
      ∀i<2,t.mem.readW (countP σ i) 64=256 := by
  rw [WP.block_append_iff]
  refine WP.mono (initTwo_ok hp) fun s ⟨he,h0⟩ => ?_
  exact initCounts_pair hp he (fun p h => by
    have : p=0 := by omega
    subst p; exact h0)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
