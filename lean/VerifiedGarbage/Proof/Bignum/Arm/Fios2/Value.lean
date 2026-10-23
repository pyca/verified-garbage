module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.PowLit

/-! The two-row identity extended by one word of each row. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Proof.Mont

theorem value_extend {mem0 mem mem' : Mem} {base : Addr} {acc b mod j a0 q0 a1 q1 C C' u : Nat}
    (prior : 2 ^ 64 * val32 mem base acc j + 2 ^ (32 * (j + 2)) * C =
      val32 mem0 base acc (j + 2) + a0 * val32 mem0 base b (j + 2) + q0 * val32 mem0 base mod (j + 2) +
        2 ^ 32 * (a1 * val32 mem0 base b (j + 1) + q1 * val32 mem0 base mod (j + 1)))
    (step : u + 2 ^ 32 * C' =
      w32 mem0 base (acc + 4 * (j + 2)) + a0 * w32 mem0 base (b + 4 * (j + 2)) +
        q0 * w32 mem0 base (mod + 4 * (j + 2)) + a1 * w32 mem0 base (b + 4 * (j + 1)) +
        q1 * w32 mem0 base (mod + 4 * (j + 1)) + C)
    (stored : val32 mem' base acc (j + 1) = val32 mem base acc j + 2 ^ (32 * j) * u) :
    2 ^ 64 * val32 mem' base acc (j + 1) + 2 ^ (32 * (j + 1 + 2)) * C' =
      val32 mem0 base acc (j + 1 + 2) + a0 * val32 mem0 base b (j + 1 + 2) +
        q0 * val32 mem0 base mod (j + 1 + 2) +
        2 ^ 32 * (a1 * val32 mem0 base b (j + 1 + 1) + q1 * val32 mem0 base mod (j + 1 + 1)) := by
  have p3 : 2 ^ (32 * (j + 2 + 1)) = 2 ^ 96 * 2 ^ (32 * j) := by
    rw [show 32 * (j + 2 + 1) = 96 + 32 * j by omega]; exact Nat.pow_add 2 96 (32 * j)
  have p2 : 2 ^ (32 * (j + 2)) = 2 ^ 64 * 2 ^ (32 * j) := by
    rw [show 32 * (j + 2) = 64 + 32 * j by omega]; exact Nat.pow_add 2 64 (32 * j)
  have p1 : 2 ^ (32 * (j + 1)) = 2 ^ 32 * 2 ^ (32 * j) := pow32_succ _
  have eT := val32_succ mem0 base acc (j + 2)
  have eB2 := val32_succ mem0 base b (j + 2)
  have eM2 := val32_succ mem0 base mod (j + 2)
  have eB1 := val32_succ mem0 base b (j + 1)
  have eM1 := val32_succ mem0 base mod (j + 1)
  rw [p2] at eT eB2 eM2 prior
  rw [p1] at eB1 eM1
  rw [show j + 1 + 2 = j + 2 + 1 by omega, show j + 1 + 1 = j + 2 by omega, p3, stored]
  rw [show j + 2 = j + 1 + 1 by omega] at eB1 eM1
  rw [eT, eB2, eM2]
  rw [show j + 1 + 1 = j + 2 by omega] at eB1 eM1
  rw [eB1, eM1] at prior ⊢
  have scaled := congrArg (fun z => 2 ^ 64 * 2 ^ (32 * j) * z) step
  generalize 2 ^ (32 * j) = P at prior scaled ⊢
  generalize val32 mem base acc j = S at prior scaled ⊢
  generalize val32 mem0 base acc (j + 2) = T at prior scaled ⊢
  generalize val32 mem0 base b (j + 1) = B at prior scaled ⊢
  generalize val32 mem0 base mod (j + 1) = M at prior scaled ⊢
  generalize w32 mem0 base (acc + 4 * (j + 2)) = wT at prior scaled ⊢
  generalize w32 mem0 base (b + 4 * (j + 2)) = wB2 at prior scaled ⊢
  generalize w32 mem0 base (mod + 4 * (j + 2)) = wM2 at prior scaled ⊢
  generalize w32 mem0 base (b + 4 * (j + 1)) = wB1 at prior scaled ⊢
  generalize w32 mem0 base (mod + 4 * (j + 1)) = wM1 at prior scaled ⊢
  grind

/-- The first words of both rows: the two cancelled words are zero. -/
theorem first_value {T0 T1 B0 B1 M0 M1 a0 a1 q0 q1 u1 u3 u4 u5 c7 c8 c7' c8' c5 c11 : Nat}
    (x1 : u1 + 2 ^ 32 * c7 = B0 * a0 + T0)
    (x2 : 0 + 2 ^ 32 * c8 = M0 * q0 + u1)
    (x3 : u3 + 2 ^ 32 * c7' = B1 * a0 + T1 + c7)
    (x4 : u4 + 2 ^ 32 * c8' = M1 * q0 + u3 + c8)
    (x5 : u5 + 2 ^ 32 * c5 = B0 * a1 + u4)
    (x6 : 0 + 2 ^ 32 * c11 = M0 * q1 + u5) :
    2 ^ 64 * (c7' + c8' + c5 + c11) =
      (T0 + 2 ^ 32 * T1) + a0 * (B0 + 2 ^ 32 * B1) + q0 * (M0 + 2 ^ 32 * M1) +
        2 ^ 32 * (a1 * B0 + q1 * M0) := by
  grind

/-- The tops of both rows complete the two-row identity. -/
theorem top_value {S S' C T Tn Tn1 B Bl M Ml a0 a1 q0 q1 W P : Nat}
    (prior : 2 ^ 64 * S + 2 ^ 64 * P * C =
      T + a0 * (B + 2 ^ 32 * P * Bl) + q0 * (M + 2 ^ 32 * P * Ml) + 2 ^ 32 * (a1 * B + q1 * M))
    (step : W = Bl * a1 + Ml * q1 + (Tn + 2 ^ 32 * Tn1) + C)
    (stored : S' = S + P * W) :
    2 ^ 64 * S' = (T + 2 ^ 64 * P * (Tn + 2 ^ 32 * Tn1)) + (a0 + 2 ^ 32 * a1) * (B + 2 ^ 32 * P * Bl) +
      (q0 + 2 ^ 32 * q1) * (M + 2 ^ 32 * P * Ml) := by
  subst stored step
  grind

end VG.Proof.Bignum.Arm.Fios2
