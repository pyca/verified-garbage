import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.Edwards.Ladder

/-! Scalar clamping and the Edwards-to-Montgomery map, shared by fixed-base implementations. -/
namespace VG.Proof.X25519.Edwards
open VG
open VG.Proof.Ed25519 (Rep dZ toZ_add toZ_sub toZ_mul toZ_pow)
open VG.Spec.X25519 (decodeScalar25519 P)
/-- A bit of the decoded scalar of 32 bytes is that of the bytes read as a
number, but for the clamped ones. -/
theorem clamped_bit {kb : List Byte} (hk : kb.length = 32) {q : Nat} (hq : q < 256) :
    (decodeScalar25519 kb / 2 ^ q) % 2 =
      if q < 3 ∨ q = 255 then 0 else if q = 254 then 1 else (Spec.Ed25519.decodeLE kb / 2 ^ q) % 2 := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.and_one_is_mod,
    ← Nat.and_one_is_mod]
  by_cases h255 : q = 255
  · subst h255
    rw [Edwards.decodeScalar25519_shift hk]; rfl
  · have hb := X25519.scalar_bit hk (t := q) (by omega)
    simp only [X25519.bit] at hb
    rw [hb, Proof.Ed25519.decodeLE_eq, X25519.leNum_bit]
    by_cases h3 : q < 3
    · simp only [h3, true_or, ↓reduceIte]
    · simp only [h3, h255, or_self, ↓reduceIte]

/-- `(Z + Y) / (Z - Y)` of a representative of `a` is `(1 + y) / (1 - y)`. -/
theorem u_rep {p : Spec.Ed25519.Point} {a : VG.Proof.Ed25519.Edwards.EPoint dZ} (h : Rep p a) :
    Proof.Ed25519.toZ ((p.Z + p.Y) * Spec.X25519.pow (p.Z - p.Y) (P - 2)) = (1 + a.y) / (1 - a.y) := by
  rw [toZ_mul, toZ_add, toZ_pow, toZ_sub, Edwards.pow_P_sub_two, h.y]
  have hz := h.z
  by_cases hy : 1 - a.y = 0
  · rw [show Proof.Ed25519.toZ p.Z - a.y * Proof.Ed25519.toZ p.Z = (1 - a.y) * Proof.Ed25519.toZ p.Z by ring,
      hy]
    simp
  · rw [show Proof.Ed25519.toZ p.Z - a.y * Proof.Ed25519.toZ p.Z = (1 - a.y) * Proof.Ed25519.toZ p.Z by ring,
      show Proof.Ed25519.toZ p.Z + a.y * Proof.Ed25519.toZ p.Z = (1 + a.y) * Proof.Ed25519.toZ p.Z by ring]
    field_simp


end VG.Proof.X25519.Edwards
