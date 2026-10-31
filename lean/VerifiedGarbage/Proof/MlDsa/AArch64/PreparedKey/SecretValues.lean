module

public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values

/-! # Each preparation slice decodes the specified secret polynomial -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Proof.MlDsa.PreparedKey

theorem secret_value (p : Params) (key : List Byte) {i : Nat}
    (hi : i < p.ℓ + 2 * p.k) :
    let (src, len, a, b) := secretPiece p i
    ntt (toRq (bitUnpack ((key.drop src).take len) a b)) =
      (preparedSecretPolys p key)[i]! := by
  have hlen : secretLen p = VG.Proof.MlDsa.Sign.lenS p := rfl
  by_cases h1 : i < p.ℓ
  · rw [secret_s1 p key h1]
    simp only [secretPiece, ite_eq_left (show i < p.ℓ + p.k by omega), hlen]
    rfl
  · by_cases h2 : i < p.ℓ + p.k
    · have hj : i - p.ℓ < p.k := by omega
      have he : p.ℓ + (i - p.ℓ) = i := by omega
      rw [← he, secret_s2 p key hj]
      simp only [secretPiece, ite_eq_left (show p.ℓ + (i - p.ℓ) < p.ℓ + p.k by omega), hlen]
      unfold VG.Proof.MlDsa.Sign.s2F
      rw [Nat.mul_add]
      congr 5 <;> omega
    · have hj : i - (p.ℓ + p.k) < p.k := by omega
      have he : p.ℓ + p.k + (i - (p.ℓ + p.k)) = i := by omega
      rw [← he, secret_t0 p key hj]
      simp only [secretPiece, ite_eq_right (show ¬ p.ℓ + p.k + (i - (p.ℓ + p.k)) < p.ℓ + p.k by omega), hlen]
      unfold VG.Proof.MlDsa.Sign.t0F
      have hoff : 128 + VG.Proof.MlDsa.Sign.lenS p * (p.ℓ + p.k) +
          416 * (p.ℓ + p.k + (i - (p.ℓ + p.k)) - p.ℓ - p.k) =
          128 + VG.Proof.MlDsa.Sign.lenS p * p.ℓ + VG.Proof.MlDsa.Sign.lenS p * p.k +
            32 * d * (i - (p.ℓ + p.k)) := by
        rw [Nat.mul_add]
        simp only [d]
        omega
      rw [hoff]
      rfl

end VG.Proof.MlDsa.AArch64.PreparedKey
