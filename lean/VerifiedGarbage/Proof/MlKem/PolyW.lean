module

public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Spec.MlKem.Kpke16

/-!
# ML-KEM: polynomials of `w`-bit words in memory, for every target

The stored representation of `Spec/MlKem/Kpke16.lean` (`coeffAtW`,
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

end VG.Proof.MlKem
