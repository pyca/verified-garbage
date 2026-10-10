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

/-- The `n` blocks at `D` in `m`: the first `k` are `F`'s, the others as in
`m₀`. -/
def DInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → List Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

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
    {n : Nat} {t : List Byte} (ht : t.length = 16) (h : DInv m₀ m D n n (ctrOut cipher m₀ D (toNat t))) :
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
