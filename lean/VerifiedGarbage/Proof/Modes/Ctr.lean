import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Spec.Cbc.Contract

/-!
# CTR's result, for any block cipher and target

`ctr_of_dinv`: when a mode's data loop has replaced each block `j` with its
XOR with the encryption of the counter block `T₁ + j` (`ctrOut`), the
blocks are `Spec.Ctr.crypt`'s. Nothing here depends on a cipher or a
target.
-/

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (ofNat toNat)

/-- CTR's output block `j`, from the data at `D` in `m₀` and the counter
block `V`: data block `j` XORed with the encryption of the counter block
`V + j`. -/
def ctrOut (cipher : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (V j : Nat) : List Byte :=
  Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16) (cipher (ofNat (V + j) 16))

/-- The `n` blocks of `L` bytes at `D` in `m`: the first `k` are `F`'s, the
others as in `m₀`. -/
def DInv (L : Nat) (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → List Byte) : Prop :=
  ∀ i < L * n, m (D + BitVec.ofNat 64 i) =
    if i < L * k then (F (i / L)).getD (i % L) 0 else m₀ (D + BitVec.ofNat 64 i)

/-- The `n` blocks of `L` bytes at `p`. -/
def blocksOf (L : Nat) (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (List.range n).map fun i => bytesAt m (p + BitVec.ofNat 64 (L * i)) L

theorem blocksOf_16 : blocksOf 16 = Spec.Cbc.blocksAt := rfl

/-! ## Indices into blocks of `L` bytes -/

theorem idx_lt {L j n : Nat} (hj : j < n) : L * j + L ≤ L * n := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj

theorem idx_div {L j u : Nat} (hu : u < L) : (L * j + u) / L = j := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu, Nat.zero_add]

theorem idx_mod {L j u : Nat} (hu : u < L) : (L * j + u) % L = u := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]

/-- Byte `i` of the blocks of `L` bytes is byte `i % L` of block `i / L`. -/
theorem idx_split {L i : Nat} (hL : 0 < L) : L * (i / L) + i % L = i ∧ i % L < L :=
  ⟨Nat.div_add_mod i L, Nat.mod_lt _ hL⟩

theorem idx_block {L i n : Nat} (hL : 0 < L) (hi : i < L * n) : i / L < n :=
  (Nat.div_lt_iff_lt_mul hL).mpr (by rw [Nat.mul_comm]; exact hi)

theorem idx_lt_iff {L i k : Nat} (hL : 0 < L) : i < L * k ↔ i / L < k := by
  rw [Nat.div_lt_iff_lt_mul hL, Nat.mul_comm]

/-- `DInv` from each block's bytes. -/
theorem dinv_of_blocks {L : Nat} (hL : 0 < L) {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → List Byte}
    (h : ∀ q < n, ∀ r < L, m (D + BitVec.ofNat 64 (L * q + r)) =
      if q < k then (F q).getD r 0 else m₀ (D + BitVec.ofNat 64 (L * q + r))) : DInv L m₀ m D n k F := by
  intro i hi
  obtain ⟨e, hr⟩ := idx_split (i := i) hL
  have h' := h (i / L) (idx_block hL hi) (i % L) hr
  rw [e] at h'
  rw [h']
  by_cases hq : i / L < k
  · rw [ite_eq_left hq, ite_eq_left ((idx_lt_iff hL).mpr hq)]
  · rw [ite_eq_right hq, ite_eq_right (mt (idx_lt_iff hL).mp hq)]

theorem ctrOut_getD {cipher : Spec.Cbc.Cipher} (hc : ∀ b, (cipher b).length = 16) (m₀ : Mem) (D : Addr)
    (V j : Nat) {u : Nat} (hu : u < 16) :
    (ctrOut cipher m₀ D V j).getD u 0 =
      m₀ (D + BitVec.ofNat 64 (16 * j + u)) ^^^ (cipher (ofNat (V + j) 16)).getD u 0 := by
  have h1 : u < (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16).length := by simp [bytesAt, hu]
  have h2 : u < (cipher (ofNat (V + j) 16)).length := by rw [hc]; exact hu
  have h3 : u < (ctrOut cipher m₀ D V j).length := by
    simp only [ctrOut, Spec.Cbc.xor, List.length_zipWith]; omega
  rw [← List.getElem_eq_getD (h := h3) 0, ← List.getElem_eq_getD (h := h2) 0]
  simp only [ctrOut, Spec.Cbc.xor, List.getElem_zipWith]
  simp [bytesAt, VG.Offset.add_add]

/-- The data after the data loop, as CTR's. -/
theorem ctr_of_dinv {cipher : Spec.Cbc.Cipher} (hc : ∀ b, (cipher b).length = 16) {m₀ m : Mem} {D : Addr}
    {n : Nat} {t : List Byte} (ht : t.length = 16) (h : DInv 16 m₀ m D n n (ctrOut cipher m₀ D (toNat t))) :
    Spec.Cbc.blocksAt m D n = Spec.Ctr.crypt cipher t (Spec.Cbc.blocksAt m₀ D n) := by
  have hl : (Spec.Cbc.blocksAt m₀ D n).length = n := by simp [Spec.Cbc.blocksAt]
  rw [Spec.Ctr.crypt, hl, AesCtr.counters_eq_map, Spec.Cbc.blocksAt, Spec.Cbc.blocksAt, List.map_map,
    List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [AesCtr.next_eq ht]
  show bytesAt m (D + BitVec.ofNat 64 (16 * j)) 16 = ctrOut cipher m₀ D (toNat t) j
  apply List.ext_getElem (by simp [bytesAt, ctrOut, Spec.Cbc.xor, hc])
  intro u h1 h2
  have hu : u < 16 := by simpa [bytesAt] using h1
  rw [show (ctrOut cipher m₀ D (toNat t) j)[u] = (ctrOut cipher m₀ D (toNat t) j).getD u 0 from
    List.getElem_eq_getD 0, ctrOut_getD hc _ _ _ _ hu]
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [VG.Offset.add_add, h _ (by omega), ite_eq_left (by omega), show (16 * j + u) / 16 = j by omega,
    show (16 * j + u) % 16 = u by omega, ctrOut_getD hc _ _ _ _ hu]

end VG.Proof.Modes
