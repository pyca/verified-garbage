import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentCounter

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64

/-- Later output blocks cannot change an already serialized rate block. -/
theorem RateBlock.keep {m m' : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    {rs : List Region} (h : RateBlock m a n A) (hn : n ≤ 10)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (Region.mk a (16*n+8)).Disjoint r) :
    RateBlock m' a n A := by
  constructor
  · intro i hi
    rw [hf.read (Offset.contains_base a (by omega) (by omega)) hd (by decide)]
    exact h.1 i hi
  · rw [hf.readW (Offset.contains_base a (by omega) (by omega)) hd (by decide)]
    exact h.2

def permuted (A : Spec.Sha3.State) : Nat → Spec.Sha3.State
  | 0 => A
  | j+1 => Spec.Sha3.keccakF (permuted A j)

/-- Output of the first `j` paired permutations. -/
def StreamOutput (m : Mem) (a : Addr) (n j : Nat) (A : Spec.Sha3.State) : Prop :=
  ∀ i < j, RateBlock m (a+BitVec.ofNat 64 ((16*n+8)*i)) n
    (permuted A (i+1))

/-- Adjacent bounded output blocks have disjoint addresses even if the base
address itself wraps. -/
theorem block_disjoint {a : Addr} {n i j : Nat} (hn : n ≤ 10)
    (hij : i < j) (hj : j < 65536) :
    (Region.mk (a+BitVec.ofNat 64 ((16*n+8)*i)) (16*n+8)).Disjoint
      ⟨a+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩ := by
  have hij' := Nat.mul_le_mul_left (16*n+8) hij
  have hiBound := Nat.mul_le_mul (show 16*n+8 ≤ 168 by omega) (show i+1 ≤ 65536 by omega)
  have hjBound := Nat.mul_le_mul (show 16*n+8 ≤ 168 by omega) (show j+1 ≤ 65536 by omega)
  simp only [Nat.mul_add,Nat.mul_one] at hij' hiBound hjBound
  exact Offset.disjoint a (Or.inl (by omega)) (by omega) (by omega)

/-- Appending a block preserves every earlier block in both streams. -/
theorem StreamOutput.append {m m' : Mem} {a b : Addr} {n j blocks : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hj : j < blocks) (hblocks : blocks ≤ 65536)
    (hd : (Region.mk a ((16*n+8)*blocks)).Disjoint ⟨b,(16*n+8)*blocks⟩)
    (ha : StreamOutput m a n j A) (hb : StreamOutput m b n j B)
    (hnewa : RateBlock m' (a+BitVec.ofNat 64 ((16*n+8)*j)) n (permuted A (j+1)))
    (hnewb : RateBlock m' (b+BitVec.ofNat 64 ((16*n+8)*j)) n (permuted B (j+1)))
    (hf : Frame [⟨a+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩,
      ⟨b+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩] m m') :
    StreamOutput m' a n (j+1) A ∧ StreamOutput m' b n (j+1) B := by
  have sub (p : Addr) (i : Nat) (hi : i < blocks) :
      (Region.mk (p+BitVec.ofNat 64 ((16*n+8)*i)) (16*n+8)).Sub
        ⟨p,(16*n+8)*blocks⟩ := by
    apply Offset.sub_base
    have h := Nat.mul_le_mul_left (16*n+8) hi
    simpa only [Nat.mul_succ] using h
  constructor
  · intro i hi
    by_cases he : i = j
    · simpa only [he] using hnewa
    · refine (ha i (by omega)).keep hn hf ?_
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact block_disjoint hn (by omega) (by omega)
      · exact (hd.sub_left (sub a i (by omega))).sub_right (sub b j hj)
  · intro i hi
    by_cases he : i = j
    · simpa only [he] using hnewb
    · refine (hb i (by omega)).keep hn hf ?_
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact (hd.symm.sub_left (sub b i (by omega))).sub_right (sub a j hj)
      · exact block_disjoint hn (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Resident
