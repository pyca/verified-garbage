import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.Cmac.Block

/-!
# AES-SIV: finishing S2V with a string of a block or more

For a last string `P` of `L ≥ 16` bytes, with `nb = ⌊(L − 1) / 16⌋` whole
blocks before its last 1 to 16 bytes, `k = max(nb, 1) − 1` (`kOf`) and
`j = min(nb, 1)` (`jOf`), an implementation copies the last `T = L − 16 k`
bytes of `P` (17 to 32 of them, or 16 if `L = 16`) to a tail and XORs `D`
into its last 16 bytes (`xorend_mem`), so the tail is `P[16k..] xorend D`;
then it chains the `k` blocks of `P`, then the first `j` blocks of the tail,
and finalizes the rest of the tail (`long_spec`). Nothing here depends on a
target.
-/

namespace VG.Proof.AesSiv

open VG

/-- The whole blocks of `P` chained before the tail. -/
def kOf (L : Nat) : Nat := if L < 17 then 0 else (L - 1) / 16 - 1

/-- The whole blocks of the tail chained before its last bytes. -/
def jOf (L : Nat) : Nat := if L < 17 then 0 else 1

theorem kOf_lt {L : Nat} (h : L < 17) : kOf L = 0 := by simp [kOf, h]

theorem kOf_ge {L : Nat} (h : ¬ L < 17) : kOf L = (L - 1) / 16 - 1 := by simp [kOf, h]

theorem kOf_tail {L : Nat} (h : 16 ≤ L) : 16 ≤ L - 16 * kOf L ∧ L - 16 * kOf L ≤ 32 := by
  unfold kOf; split <;> omega

theorem jOf_rest {L : Nat} (h : 16 ≤ L) :
    16 * jOf L ≤ L - 16 * kOf L ∧ 0 < L - 16 * kOf L - 16 * jOf L ∧ L - 16 * kOf L - 16 * jOf L ≤ 16 := by
  unfold kOf jOf; split <;> omega

theorem jOf_le (L : Nat) : jOf L ≤ 1 := by unfold jOf; split <;> omega

/-- XORing `D` into the last 16 of `T` bytes. -/
theorem xorend_mem (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (Proof.Cmac.xor2Mem m (B + BitVec.ofNat 64 (T - 16)) (B + BitVec.ofNat 64 (T - 16)) Q) B T =
      Spec.Siv.xorend (Spec.Aes.bytesAt m B T) (Spec.Aes.bytesAt m Q 16) := by
  have hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega)
  have e : T = (T - 16) + 16 := by omega
  have hs := Proof.Cmac.Stream.bytesAt_append (Proof.Cmac.xor2Mem m (B + BitVec.ofNat 64 (T - 16))
    (B + BitVec.ofNat 64 (T - 16)) Q) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  have tk := take_bytesAt m B (a := T - 16) (b := 16)
  have dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor2Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega) (by omega)) (by omega),
    Proof.Cmac.xor2Mem_bytes _ ?_ ?_, Siv.xor_eq]
  · rw [Offset.add_add]; exact Offset.disjoint B (by omega) (by omega) (by omega)
  · exact (hd.sub_left (fun a ha => hc a (Region.sub_prefix (base := B + BitVec.ofNat 64 (T - 16)) (len := 8)
      (len' := 16) (by decide) a ha))).sub_right (Offset.sub_base Q (d := 8) (n := 8) (k := 16) (by decide))

/-- S2V's end for a string of a block or more, as the implementations
compute it. -/
theorem long_spec (ciph : Spec.Cmac.Cipher) (k1 k2 d p : List Byte) (hd : d.length = 16) (hL16 : 16 ≤ p.length) :
    ciph (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 k1 k2
          ((Spec.Siv.xorend (p.drop (16 * kOf p.length)) d).drop (16 * jOf p.length)))
        (Spec.Cmac.chain ciph (Spec.Cmac.chain ciph (Spec.Cmac.zeros 16)
            (Spec.Cmac.blocks 16 (p.take (16 * kOf p.length))))
          (Spec.Cmac.blocks 16 ((Spec.Siv.xorend (p.drop (16 * kOf p.length)) d).take (16 * jOf p.length))))) =
      Spec.Siv.s2vFinish (Spec.Siv.cmacWith ciph k1 k2) d p := by
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hlT : (Spec.Siv.xorend (p.drop (16 * kOf p.length)) d).length = p.length - 16 * kOf p.length := by
    rw [Siv.length_xorend (by rw [List.length_drop, hd]; omega), List.length_drop]
  rw [Siv.s2vFinish_long _ hd (a := 16 * kOf p.length) (by omega)]
  generalize Spec.Siv.xorend (List.drop (16 * kOf p.length) p) d = tl at hlT ⊢
  conv => rhs; rw [← List.take_append_drop (16 * jOf p.length) tl]
  rw [← List.append_assoc, Siv.cmacWith_split₂ _ _ _ (by rw [List.length_take]; omega)
      (by rw [List.length_take, hlT]; omega) (by rw [List.length_drop, hlT]; omega)
      (Or.inr (by rw [List.length_drop, hlT]; omega)), Proof.Cmac.xor_comm]

end VG.Proof.AesSiv
