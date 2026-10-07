import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

namespace VG.Proof.Bignum.X86_64.AdxRotate8
theorem combine {a0 a1 a2 a3 a4 a5 a6 a7 p0 p1 p2 p3 p4 p5 p6 p7 h0 h1 h2 h3 h4 h5 h6 h7 l0 l1 l2 l3 l4 l5 l6 l7 l8 c0 c1 c2 c3 c4 c5 c6 c7 o0 o1 o2 o3 o4 o5 o6 ct ot : Nat}
    (e0 : l0 + 2 ^ 64 * c0 + 2 ^ 64 * h0 + 2 ^ 128 * o0 = a0 + p0 + 0 + 2 ^ 64 * a1 + 2 ^ 64 * 0)
    (e1 : l1 + 2 ^ 64 * c1 + 2 ^ 64 * h1 + 2 ^ 128 * o1 = h0 + p1 + c0 + 2 ^ 64 * a2 + 2 ^ 64 * o0)
    (e2 : l2 + 2 ^ 64 * c2 + 2 ^ 64 * h2 + 2 ^ 128 * o2 = h1 + p2 + c1 + 2 ^ 64 * a3 + 2 ^ 64 * o1)
    (e3 : l3 + 2 ^ 64 * c3 + 2 ^ 64 * h3 + 2 ^ 128 * o3 = h2 + p3 + c2 + 2 ^ 64 * a4 + 2 ^ 64 * o2)
    (e4 : l4 + 2 ^ 64 * c4 + 2 ^ 64 * h4 + 2 ^ 128 * o4 = h3 + p4 + c3 + 2 ^ 64 * a5 + 2 ^ 64 * o3)
    (e5 : l5 + 2 ^ 64 * c5 + 2 ^ 64 * h5 + 2 ^ 128 * o5 = h4 + p5 + c4 + 2 ^ 64 * a6 + 2 ^ 64 * o4)
    (e6 : l6 + 2 ^ 64 * c6 + 2 ^ 64 * h6 + 2 ^ 128 * o6 = h5 + p6 + c5 + 2 ^ 64 * a7 + 2 ^ 64 * o5)
    (e7 : l7 + 2 ^ 64 * h7 + 2 ^ 64 * c7 = h6 + p7 + c6)
    (e8 : l8 + 2 ^ 64 * ct + 2 ^ 64 * ot = h7 + c7 + o6) :
    l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3 + 2 ^ 256 * l4 + 2 ^ 320 * l5 + 2 ^ 384 * l6 + 2 ^ 448 * l7 + 2 ^ 512 * l8 + 2 ^ 576 * (ct + ot) =
      a0 + p0 + 2 ^ 64 * (a1 + p1) + 2 ^ 128 * (a2 + p2) + 2 ^ 192 * (a3 + p3) + 2 ^ 256 * (a4 + p4) + 2 ^ 320 * (a5 + p5) + 2 ^ 384 * (a6 + p6) + 2 ^ 448 * (a7 + p7) := by
  omega
theorem extend_blocks {P R L C X T U N O C' A B : Nat}
    (h : L + P * C = X + T + U * N) (h' : O + R * C' = C + A + U * B) :
    L + P * O + P * R * C' = X + (T + P * A) + U * (N + P * B) := by
  grind
theorem tile_combine {R P H A U N₀ L C T N₁ Y K V Q : Nat}
    (h₀ : R * H = A + U * N₀) (h₁ : L + P * C = H + T + U * N₁)
    (h₂ : Y + R * K = C + V + Q) :
    R * (L + P * Y + (P * R) * K) =
      (A + R * T + (P * R) * V) + (P * R) * Q + U * (N₀ + R * N₁) := by
  grind
theorem extend_high {R P X Y C D U N H : Nat}
    (h : R * (X + P * C) = Y + P * D + U * N) :
    R * (X + P * H + P * C) = Y + (P * R) * H + P * D + U * N := by
  grind
theorem radix_bound {q P u R : Nat} (hq : q < P) (hu : u < R) : q + P * u < P * R := by
  have h := Nat.mul_le_mul_left P (show u + 1 ≤ R by omega)
  rw [Nat.mul_add, Nat.mul_one] at h
  omega

theorem extend_tiles {P R X Y T q u N : Nat}
    (h : P * X = T + q * N) (h' : R * Y = X + u * N) :
    (P * R) * Y = T + (q + P * u) * N := by
  grind
end VG.Proof.Bignum.X86_64.AdxRotate8
