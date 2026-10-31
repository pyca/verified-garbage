module

public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: ECB and CTR share a target-independent memory invariant.
/-! # Processing consecutive AES blocks in memory -/

@[expose] public section
namespace VG.Proof.Aes.Memory
open VG

/-- The first `k` blocks hold `F`; later blocks still hold the input. -/
def Processed (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16*n, m (D + BitVec.ofNat 64 i) =
    if i < 16*k then (F (i/16)).getD (i%16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem Processed.refl (m : Mem) (D : Addr) (n : Nat) (F : Nat → Spec.Aes.State) :
    Processed m m D n 0 F := by
  intro i _
  simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]

theorem Processed.original {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    (h : Processed m₀ m D n k F) {j : Nat} (hj : k ≤ j) (hjn : j < n) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16*j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16*j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_right (show ¬16*j+i < 16*k by omega)]

theorem Processed.store {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 128}
    (hn : 16*n ≤ 2^64) (hk : k < n) (h : Processed m₀ m D n k F)
    (hv : ∀ t < 16, v.extractLsb' (8*t) 8 = (F k).getD t 0) :
    Processed m₀ (m.write (D + BitVec.ofNat 64 (16*k)) 16 v) D n (k+1) F ∧
      Frame [⟨D, 16*n⟩] m (m.write (D + BitVec.ofNat 64 (16*k)) 16 v) := by
  refine ⟨?_, (Frame.refl _ m).write (List.mem_singleton_self _) v
    (Offset.contains_base D (d := 16*k) (n := 16) (k := 16*n) (by omega) (by omega))⟩
  intro i hi
  rw [Mem.write, Offset.sub_toNat' D (by omega) (by omega)]
  by_cases h1 : 16*k ≤ i
  · rw [ite_eq_left h1]
    by_cases h2 : i-16*k < 16
    · rw [ite_eq_left h2, hv _ h2, ite_eq_left (show i < 16*(k+1) by omega),
        show i/16 = k by omega, show i%16 = i-16*k by omega]
    · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬i < 16*k by omega),
        ite_eq_right (show ¬i < 16*(k+1) by omega)]
  · rw [ite_eq_right h1, ite_eq_right (show ¬2^64+i-16*k < 16 by omega), h i hi,
      ite_eq_left (show i < 16*k by omega), ite_eq_left (show i < 16*(k+1) by omega)]

theorem Processed.stateAt {m₀ m : Mem} {D : Addr} {n k j : Nat} {F : Nat → Spec.Aes.State}
    (h : Processed m₀ m D n k F) (hj : j < k) (hkn : k ≤ n) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16*j)) = F j := by
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_left (show 16*j+t < 16*k by omega),
    show (16*j+t)/16 = j by omega, show (16*j+t)%16 = t by omega]
  simp [Vector.getD, ht]

theorem Processed.statesAt {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : Processed m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  exact h.stateAt hj (Nat.le_refl _)

/-- Stores to disjoint regions preserve the completed and pending data bytes. -/
theorem Processed.frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {rs : List Region}
    (h : Processed m₀ m D n k F) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨D, 16*n⟩ : Region).Disjoint r) (hn : 16*n ≤ 2^64) :
    Processed m₀ m' D n k F := by
  intro i hi
  rw [hf.bytes (R := ⟨D, 16*n⟩) hd hn hi]
  exact h i hi

/-- A disjoint key schedule survives stores to the data buffer. -/
theorem bytesAt_frame {m m' : Mem} {R : Region} {D : Addr} {n L : Nat}
    (h : Frame [⟨D, 16*n⟩] m m') (hd : R.Disjoint ⟨D, 16*n⟩)
    (hL : L ≤ R.len) (hR : R.len ≤ 2^64) :
    Spec.Aes.bytesAt m' R.base L = Spec.Aes.bytesAt m R.base L := by
  apply List.ext_getElem
  · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range]
  · intro i hi hi'
    have hiL : i < L := by simpa only [Spec.Aes.bytesAt, List.length_map, List.length_range] using hi
    simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
    exact h.bytes (by simpa only [List.mem_singleton, forall_eq] using hd) hR (by omega)

end VG.Proof.Aes.Memory
