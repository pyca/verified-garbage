import VerifiedGarbage.Proof.Modes.Ctr

/-!
# CBC decryption's result, for any block cipher and target

`cbc_of_dinv`: when a mode's data loop has replaced each block `j` with
`CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁` (`cbcOut`, with `C₋₁` the IV), the blocks are
`Spec.Cbc.decrypt`'s. Nothing here depends on a cipher or a target.
-/

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

/-- The chaining value before block `j`: the IV, or ciphertext block `j - 1`
at `D` in `m₀`. -/
def cbcPrev (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) : List Byte :=
  if j = 0 then iv else bytesAt m₀ (D + BitVec.ofNat 64 (16 * (j - 1))) 16

/-- CBC decryption's output block `j`, from the data at `D` in `m₀`. -/
def cbcOut (ciphInv : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) : List Byte :=
  Spec.Cbc.xor (ciphInv (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16)) (cbcPrev m₀ D iv j)

theorem cbcPrev_length (m₀ : Mem) (D : Addr) {iv : List Byte} (hiv : iv.length = 16) (j : Nat) :
    (cbcPrev m₀ D iv j).length = 16 := by
  unfold cbcPrev; split
  · exact hiv
  · simp [bytesAt]

theorem cbcOut_getD {ciphInv : Spec.Cbc.Cipher} (hc : ∀ b, (ciphInv b).length = 16) (m₀ : Mem) (D : Addr)
    {iv : List Byte} (hiv : iv.length = 16) (j : Nat) {u : Nat} (hu : u < 16) :
    (cbcOut ciphInv m₀ D iv j).getD u 0 =
      (ciphInv (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16)).getD u 0 ^^^ (cbcPrev m₀ D iv j).getD u 0 := by
  have h1 : u < (ciphInv (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16)).length := by rw [hc]; exact hu
  have h2 : u < (cbcPrev m₀ D iv j).length := by rw [cbcPrev_length m₀ D hiv]; exact hu
  have h3 : u < (cbcOut ciphInv m₀ D iv j).length := by
    simp only [cbcOut, Spec.Cbc.xor, List.length_zipWith]; omega
  rw [← List.getElem_eq_getD (h := h3) 0, ← List.getElem_eq_getD (h := h1) 0,
    ← List.getElem_eq_getD (h := h2) 0]
  simp only [cbcOut, Spec.Cbc.xor, List.getElem_zipWith]

/-- `Spec.Cbc.decrypt`, block by block. -/
theorem decrypt_eq (ciphInv : Spec.Cbc.Cipher) :
    ∀ (cs : List (List Byte)) (iv : List Byte), Spec.Cbc.decrypt ciphInv iv cs =
      (List.range cs.length).map fun j =>
        Spec.Cbc.xor (ciphInv (cs.getD j [])) (if j = 0 then iv else cs.getD (j - 1) [])
  | [], _ => rfl
  | c :: cs, iv => by
    rw [Spec.Cbc.decrypt, decrypt_eq ciphInv cs c, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congrArg _ (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply, List.getD_cons_succ, Nat.succ_ne_zero, ite_false]
    cases j <;> simp

/-- The data after the data loop, as CBC decryption's. -/
theorem cbc_of_dinv {ciphInv : Spec.Cbc.Cipher} (hc : ∀ b, (ciphInv b).length = 16) {m₀ m : Mem} {D : Addr}
    {n : Nat} {iv : List Byte} (hiv : iv.length = 16) (h : DInv m₀ m D n n (cbcOut ciphInv m₀ D iv)) :
    Spec.Cbc.blocksAt m D n = Spec.Cbc.decrypt ciphInv iv (Spec.Cbc.blocksAt m₀ D n) := by
  have hl : (Spec.Cbc.blocksAt m₀ D n).length = n := by simp [Spec.Cbc.blocksAt]
  have hg : ∀ j < n, (Spec.Cbc.blocksAt m₀ D n).getD j [] = bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16 :=
    fun j hj => by simp [Spec.Cbc.blocksAt, List.getD_eq_getElem?_getD, hj]
  rw [decrypt_eq, hl, Spec.Cbc.blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  rw [hg j hj, show (if j = 0 then iv else (Spec.Cbc.blocksAt m₀ D n).getD (j - 1) []) = cbcPrev m₀ D iv j by
    unfold cbcPrev; split
    · rfl
    · rw [hg _ (by omega)]]
  show bytesAt m (D + BitVec.ofNat 64 (16 * j)) 16 = cbcOut ciphInv m₀ D iv j
  apply List.ext_getElem (by simp [bytesAt, cbcOut, Spec.Cbc.xor, hc, cbcPrev_length m₀ D hiv])
  intro u h1 h2
  have hu : u < 16 := by simpa [bytesAt] using h1
  rw [show (cbcOut ciphInv m₀ D iv j)[u] = (cbcOut ciphInv m₀ D iv j).getD u 0 from List.getElem_eq_getD 0]
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [VG.Offset.add_add, h _ (by omega), ite_eq_left (by omega), show (16 * j + u) / 16 = j by omega,
    show (16 * j + u) % 16 = u by omega]

end VG.Proof.Modes
