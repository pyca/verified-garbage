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

/-- CBC encryption's ciphertext block `j` (of `L` bytes), from the data at
`D` in `m₀`. -/
def cbcEncC (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) : Nat → List Byte
  | 0 => ciph (Spec.Cbc.xor (bytesAt m₀ D L) iv)
  | j + 1 => ciph (Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (j + 1))) L) (cbcEncC L ciph m₀ D iv j))

/-- The chaining value before block `j`: the IV, or ciphertext block `j - 1`. -/
def cbcEncPrev (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) : List Byte :=
  if j = 0 then iv else cbcEncC L ciph m₀ D iv (j - 1)

theorem cbcEncC_eq (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) :
    cbcEncC L ciph m₀ D iv j =
      ciph (Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * j)) L) (cbcEncPrev L ciph m₀ D iv j)) := by
  cases j
  · simp [cbcEncC, cbcEncPrev]
  · simp [cbcEncC, cbcEncPrev]

theorem cbcEncC_shift (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) :
    ∀ j, cbcEncC L ciph m₀ D iv (j + 1) =
      cbcEncC L ciph m₀ (D + BitVec.ofNat 64 L) (cbcEncC L ciph m₀ D iv 0) j
  | 0 => by simp [cbcEncC]
  | j + 1 => by
    show ciph (Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (j + 1 + 1))) L) (cbcEncC L ciph m₀ D iv (j + 1))) =
      ciph (Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 L + BitVec.ofNat 64 (L * (j + 1))) L)
        (cbcEncC L ciph m₀ (D + BitVec.ofNat 64 L) (cbcEncC L ciph m₀ D iv 0) j))
    rw [cbcEncC_shift L ciph m₀ D iv j, VG.Offset.add_add, show L + L * (j + 1) = L * (j + 1 + 1) by
      rw [Nat.mul_succ L (j + 1)]; omega]

theorem blocksOf_succ (L : Nat) (m : Mem) (D : Addr) (n : Nat) :
    blocksOf L m D (n + 1) = bytesAt m D L :: blocksOf L m (D + BitVec.ofNat 64 L) n := by
  simp only [blocksOf, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congr (congrArg List.cons (by simp)) (List.map_congr_left fun j _ => ?_)
  simp only [Function.comp_apply]
  rw [VG.Offset.add_add, Nat.mul_succ, Nat.add_comm]

/-- `Spec.Cbc.encrypt`, block by block. -/
theorem encrypt_eq (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) :
    ∀ (n : Nat) (D : Addr) (iv : List Byte), Spec.Cbc.encrypt ciph iv (blocksOf L m₀ D n) =
      (List.range n).map (cbcEncC L ciph m₀ D iv)
  | 0, _, _ => rfl
  | n + 1, D, iv => by
    rw [blocksOf_succ, Spec.Cbc.encrypt, encrypt_eq L ciph m₀ n, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congr (congrArg List.cons rfl) (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply]
    rw [cbcEncC_shift]
    rfl

/-- The data after the data loop, as CBC encryption's. -/
theorem cbcEnc_of_dinv {L : Nat} {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L) {m₀ m : Mem}
    {D : Addr} {n : Nat} {iv : List Byte} (h : DInv L m₀ m D n n (cbcEncC L ciph m₀ D iv)) :
    blocksOf L m D n = Spec.Cbc.encrypt ciph iv (blocksOf L m₀ D n) := by
  rw [encrypt_eq, blocksOf_of_dinv (fun k => by cases k <;> exact hc _) h]

end VG.Proof.Modes
