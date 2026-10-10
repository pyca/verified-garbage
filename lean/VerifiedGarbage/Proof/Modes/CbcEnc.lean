import VerifiedGarbage.Proof.Modes.Cbc

/-!
# CBC encryption's result, for any block cipher and target

`cbcEnc_of_dinv`: when a mode's data loop has replaced each block `j` with
`Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)` (`cbcEncC`, with `C₋₁` the IV), the blocks are
`Spec.Cbc.encrypt`'s. Nothing here depends on a cipher or a target.
-/

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

/-- CBC encryption's ciphertext block `j`, from the data at `D` in `m₀`. -/
def cbcEncC (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) : Nat → List Byte
  | 0 => ciph (Spec.Cbc.xor (bytesAt m₀ D 16) iv)
  | j + 1 => ciph (Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (16 * (j + 1))) 16) (cbcEncC ciph m₀ D iv j))

/-- The chaining value before block `j`: the IV, or ciphertext block `j - 1`. -/
def cbcEncPrev (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) : List Byte :=
  if j = 0 then iv else cbcEncC ciph m₀ D iv (j - 1)

theorem cbcEncC_eq (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) :
    cbcEncC ciph m₀ D iv j =
      ciph (Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16) (cbcEncPrev ciph m₀ D iv j)) := by
  cases j
  · simp [cbcEncC, cbcEncPrev]
  · simp [cbcEncC, cbcEncPrev]

theorem cbcEncC_shift (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) :
    ∀ j, cbcEncC ciph m₀ D iv (j + 1) =
      cbcEncC ciph m₀ (D + BitVec.ofNat 64 16) (cbcEncC ciph m₀ D iv 0) j
  | 0 => by simp [cbcEncC]
  | j + 1 => by
    show ciph (Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (16 * (j + 1 + 1))) 16) (cbcEncC ciph m₀ D iv (j + 1))) =
      ciph (Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * (j + 1))) 16)
        (cbcEncC ciph m₀ (D + BitVec.ofNat 64 16) (cbcEncC ciph m₀ D iv 0) j))
    rw [cbcEncC_shift ciph m₀ D iv j, VG.Offset.add_add, show 16 + 16 * (j + 1) = 16 * (j + 1 + 1) by omega]

theorem blocksAt_succ (m : Mem) (D : Addr) (n : Nat) :
    Spec.Cbc.blocksAt m D (n + 1) = bytesAt m D 16 :: Spec.Cbc.blocksAt m (D + BitVec.ofNat 64 16) n := by
  simp only [Spec.Cbc.blocksAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congr (congrArg List.cons (by simp)) (List.map_congr_left fun j _ => ?_)
  simp only [Function.comp_apply]
  rw [VG.Offset.add_add, show 16 * (j + 1) = 16 + 16 * j by omega]

/-- `Spec.Cbc.encrypt`, block by block. -/
theorem encrypt_eq (ciph : Spec.Cbc.Cipher) (m₀ : Mem) :
    ∀ (n : Nat) (D : Addr) (iv : List Byte), Spec.Cbc.encrypt ciph iv (Spec.Cbc.blocksAt m₀ D n) =
      (List.range n).map (cbcEncC ciph m₀ D iv)
  | 0, _, _ => rfl
  | n + 1, D, iv => by
    rw [blocksAt_succ, Spec.Cbc.encrypt, encrypt_eq ciph m₀ n, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congr (congrArg List.cons rfl) (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply]
    rw [cbcEncC_shift]
    rfl

/-- The data after the data loop, as CBC encryption's. -/
theorem cbcEnc_of_dinv {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16) {m₀ m : Mem} {D : Addr}
    {n : Nat} {iv : List Byte} (h : DInv m₀ m D n n (cbcEncC ciph m₀ D iv)) :
    Spec.Cbc.blocksAt m D n = Spec.Cbc.encrypt ciph iv (Spec.Cbc.blocksAt m₀ D n) := by
  rw [encrypt_eq, Spec.Cbc.blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have hl : ∀ k, (cbcEncC ciph m₀ D iv k).length = 16 := fun k => by cases k <;> exact hc _
  apply List.ext_getElem (by simp [bytesAt, hl])
  intro u h1 h2
  have hu : u < 16 := by simpa [bytesAt] using h1
  rw [show (cbcEncC ciph m₀ D iv j)[u] = (cbcEncC ciph m₀ D iv j).getD u 0 from List.getElem_eq_getD 0]
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [VG.Offset.add_add, h _ (by omega), ite_eq_left (by omega), show (16 * j + u) / 16 = j by omega,
    show (16 * j + u) % 16 = u by omega]

end VG.Proof.Modes
