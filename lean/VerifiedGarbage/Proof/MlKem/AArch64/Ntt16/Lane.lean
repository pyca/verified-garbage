module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ML-KEM's 16-bit NTT on AArch64: one lane

The product `a · z mod q` of the 16-bit NTT (`Impl/MlKem/AArch64/Ntt16.lean`):
`r = a · z - t · q` with `t = sqrdmulh(a, tw z)` is `a · z` modulo `q`, and
less than `q` in absolute value (`mm_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16

/-- The integer core: with `C = tw z` and `T = ⌊(2AC + 2¹⁵) / 2¹⁶⌋`,
`|A z - T q| < q`. -/
theorem core {A z : Int} (hA : -32768 < A) (hA' : A < 32768) :
    -3329 < A * z - (2 * A * ((z * 65536 + 3329) / 6658) + 32768) / 65536 * 3329 ∧
    A * z - (2 * A * ((z * 65536 + 3329) / 6658) + 32768) / 65536 * 3329 < 3329 := by
  generalize hC : (z * 65536 + 3329) / 6658 = C
  have hd1 : -3329 ≤ z * 65536 - 6658 * C := by omega
  have hd2 : z * 65536 - 6658 * C < 3329 := by omega
  generalize hd : z * 65536 - 6658 * C = d at hd1 hd2
  have hn : (A * d).natAbs ≤ 32767 * 3329 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
  have hQ1 : A * d ≤ 32767 * 3329 := by omega
  have hQ2 : -(32767 * 3329) ≤ A * d := by omega
  have hX : A * z * 65536 = 6658 * (A * C) + A * d := by rw [← hd]; grind
  have h2 : 2 * A * C = 2 * (A * C) := by grind
  rw [h2]
  generalize A * C = P at hX
  generalize A * d = Q at hQ1 hQ2 hX
  generalize A * z = X at hX ⊢
  omega

theorem tw_lt {z : Nat} (hz : z < 3329) : tw z < 32768 := by
  unfold tw; omega

theorem tw_def (z : Nat) : (tw z : Int) = ((z : Int) * 65536 + 3329) / 6658 := by
  unfold tw; omega

/-- The product of a lane `a` by the zeta `z`: `t = sqrdmulh(a, tw z)` exists,
and `r = a · z - t · q` is `a · z` modulo `q` and less than `q` in absolute
value. -/
theorem mm_ok (a : BitVec 16) {z : Nat} (ha : -32768 < a.toInt) (hz : z < 3329) :
    ∃ t, sqdmulhHLane true a (BitVec.ofNat 16 (tw z)) = some t ∧
      -3329 < (a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt ∧
      (a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt < 3329 ∧
      ((a * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329).toInt - a.toInt * z) % 3329 = 0 := by
  have htw := tw_lt hz
  have hc : (BitVec.ofNat 16 (tw z)).toInt = tw z := by
    rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; omega
  have hzt : (BitVec.ofNat 16 z).toInt = z := by
    rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; omega
  have hq : (BitVec.ofNat 16 3329).toInt = 3329 := by decide
  have hne : ¬ (a = 0x8000#16 ∧ BitVec.ofNat 16 (tw z) = 0x8000#16) := by
    rintro ⟨-, h⟩
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega
  have hA' : a.toInt < 32768 := BitVec.toInt_lt
  refine ⟨_, by simp only [sqdmulhHLane, hne, ite_false]; rfl, ?_⟩
  have h := core (A := a.toInt) (z := z) ha hA'
  simp only [BitVec.toInt_sub, BitVec.toInt_mul, BitVec.toInt_ofInt, hc, hzt, hq, tw_def]
  rw [Int.shiftRight_eq_div_pow] 
  simp only [ite_true, show (2 : Int) ^ 15 = 32768 from rfl]
  generalize (2 * a.toInt * (((z : Int) * 65536 + 3329) / 6658) + 32768) / 65536 = T at *
  generalize a.toInt * (z : Int) = X at *
  simp only [Int.bmod_def]
  omega

end VG.Proof.MlKem.AArch64.Ntt16
