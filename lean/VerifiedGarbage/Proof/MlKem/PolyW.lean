module

public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM: polynomials of `w`-bit words in memory, for every target

The stored representation of `Proof/MlKem/Kpke16Contract.lean` (`coeffAtW`,
`polyAtW`, `ReducedW`, `PolyIsW`): a coefficient of a reduced polynomial is
its stored word, and a polynomial of `u16`s is unchanged by writes outside
its 512 bytes.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- Coefficient `i` of `polyAtW`: the stored word modulo `q`. -/
theorem polyAtW_get (w : Nat) (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAtW w m p)[i]! = ofNat (coeffAtW w m p i).toNat := by
  rw [getElem!_eq _ hi]
  simp only [polyAtW, Vector.getElem_ofFn]

/-- The word stored for coefficient `i` of `f`. -/
theorem polyIsW_toNat {w : Nat} {m : Mem} {p : Addr} {f : Poly} (h : PolyIsW w m p f) {i : Nat} (hi : i < n) :
    (coeffAtW w m p i).toNat = (f[i]!).val := by
  rw [← h.2, polyAtW_get w m p hi, ofNat_of_lt (h.1 i hi)]

/-- Coefficient `i` of a polynomial of `u16`s is the word at `p + 2i`. -/
theorem coeffAtW16_eq (m : Mem) (p : Addr) (i : Nat) :
    coeffAtW 16 m p i = m.readW (p + BitVec.ofNat 64 (2 * i)) 16 := rfl

theorem coeffAtW16_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 512, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAtW 16 m' p i = coeffAtW 16 m p i := by
  rw [n_eq] at hi
  refine Mem.readW_congr fun k hk => ?_
  rw [show 16 / 8 * i = 2 * i from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem polyIsW16_congr {m m' : Mem} {p : Addr} {f : Poly}
    (h : ∀ k < 512, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIsW 16 m p f) :
    PolyIsW 16 m' p f :=
  ⟨fun i hi => by rw [coeffAtW16_congr h hi]; exact hf.1 i hi,
    (ext_getElem! fun i hi => by rw [polyAtW_get _ _ _ hi, polyAtW_get _ _ _ hi, coeffAtW16_congr h hi]).trans hf.2⟩

/-- A polynomial of `u16`s, in memory that writes elsewhere kept. -/
theorem polyIsW16_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {f : Poly}
    (hd : ∀ r ∈ rs, (⟨p, 512⟩ : Region).Disjoint r) (h : PolyIsW 16 m p f) : PolyIsW 16 m' p f :=
  polyIsW16_congr (bytes_frame hf hd (by decide)) h

theorem polyAtW16_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 512, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) : polyAtW 16 m' p = polyAtW 16 m p :=
  ext_getElem! fun i hi => by rw [polyAtW_get _ _ _ hi, polyAtW_get _ _ _ hi, coeffAtW16_congr h hi]

/-- Polynomial `j` of `u16`s from `p` lies within the `512 l` bytes from `p`, for `j < l`. -/
theorem w16_at {m m' : Mem} {p : Addr} {l : Nat}
    (h : ∀ i < 512 * l, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) {j : Nat} (hj : j < l) :
    ∀ k < 512, m' (p + BitVec.ofNat 64 (32 * 16 * j) + BitVec.ofNat 64 k) =
      m (p + BitVec.ofNat 64 (32 * 16 * j) + BitVec.ofNat 64 k) := fun k hk => by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

/-- The vector of `u16`s from `p`, in memory that agrees on its bytes. -/
theorem vecAtW16_congr {m m' : Mem} {p : Addr} {l : Nat}
    (h : ∀ i < 512 * l, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : vecAtW 16 m' p l = vecAtW 16 m p l :=
  List.map_congr_left fun _ hj => polyAtW16_congr (w16_at h (List.mem_range.mp hj))

theorem vecReducedW16_congr {m m' : Mem} {p : Addr} {l : Nat}
    (h : ∀ i < 512 * l, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    VecReducedW 16 m' p l ↔ VecReducedW 16 m p l :=
  ⟨fun r _ hj i hi => by rw [← coeffAtW16_congr (w16_at h hj) hi]; exact r _ hj i hi,
    fun r _ hj i hi => by rw [coeffAtW16_congr (w16_at h hj) hi]; exact r _ hj i hi⟩

/-- The `k × k` matrix of `u16`s from `p`, in memory that agrees on its bytes. -/
theorem matAtW16_congr {m m' : Mem} {p : Addr} {k : Nat}
    (h : ∀ i < 512 * (k * k), m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    matAtW 16 m' p k = matAtW 16 m p k :=
  List.map_congr_left fun r hr => vecAtW16_congr fun i hi => by
    have hr := List.mem_range.mp hr
    have : k * r + k ≤ k * k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left k hr
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h _ (by
      rw [show 32 * 16 * (k * r) + i = 512 * (k * r) + i by omega]
      have := Nat.mul_le_mul_left 512 this
      omega)

theorem vecAtW_length (w : Nat) (m : Mem) (p : Addr) (k : Nat) : (vecAtW w m p k).length = k := by
  simp [vecAtW]

theorem vecAtW16_get (m : Mem) (p : Addr) {k j : Nat} (hj : j < k) :
    (vecAtW 16 m p k)[j]! = polyAtW 16 m (p + BitVec.ofNat 64 (512 * j)) := by
  rw [getElem!_pos _ j (by rw [vecAtW_length]; exact hj)]
  simp [vecAtW]

end VG.Proof.MlKem
