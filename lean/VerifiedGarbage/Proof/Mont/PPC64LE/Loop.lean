module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Montgomery arithmetic on PPC64LE: the arithmetic of a row of the multiplication

A row adds `u [b]` and then `q m` to the accumulator `T < 2m`, for
`q = t₀ m' mod 2⁶⁴`, which makes the sum's low word zero: the sum is below
`2⁶⁴ (2m)` (`row_lt`), and `rowM_math` is the equation of the second row
with the sum moved one word down. `eval_nonzero_ofNat` evaluates the loop's
condition on a count.
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T u B q m : Nat} (hT : T < 2 * m) (hu : u < 2 ^ 64) (hB : B < m) (hq : q < 2 ^ 64) :
    T + u * B + q * m < 2 ^ 64 * (2 * m) := by
  have h1 : u * B ≤ (2 ^ 64 - 1) * B := Nat.mul_le_mul_right _ (by omega_arith)
  have h2 : q * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_right _ (by omega_arith)
  have h3 : (2 ^ 64 - 1) * B ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_left _ (by omega_arith)
  omega_arith

/-- The arithmetic of `rowM`: the accumulator, one word down, and the carry
out, times `2⁶⁴`, are the sum `T₁ + q m`. -/
theorem rowM_math {T1 t0 W F m m0 M' q r4 L5 r5 V ca R : Nat}
    (hT1 : T1 = t0 + 2 ^ 64 * (W + R * F)) (hm : m = m0 + 2 ^ 64 * M')
    (h4 : 2 ^ 64 * r4 = q * m0 + t0) (h5 : L5 + R * r5 = W + q * M' + r4) (h6 : V + 2 ^ 128 * ca = F + r5) :
    2 ^ 64 * (L5 + R * V) + 2 ^ 64 * R * 2 ^ 128 * ca = T1 + q * m := by
  subst hT1 hm
  have e : 2 ^ 64 * (L5 + R * V) + 2 ^ 64 * R * 2 ^ 128 * ca = 2 ^ 64 * (L5 + R * r5) + 2 ^ 64 * R * F := by
    rw [show 2 ^ 64 * R * 2 ^ 128 * ca = 2 ^ 64 * R * (2 ^ 128 * ca) by grind]
    have := congrArg (2 ^ 64 * R * ·) h6
    simp only [Nat.mul_add] at this
    grind
  rw [e, h5]
  grind

/-! ## An iteration -/

end VG.Proof.Mont.PPC64LE

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

theorem eval_nonzero_ofNat {s : State} {r : Reg} {x : Nat} (h : s.gpr r = BitVec.ofNat 64 x) (hx : x < 2 ^ 64) :
    isa.eval (.nonzero .d r) s = some (decide (x ≠ 0)) := by
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, h, Option.some.injEq]
  by_cases hx0 : x = 0
  · subst hx0; rfl
  · have : BitVec.ofNat 64 x ≠ 0 := fun e => hx0 (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this)
    exact (bne_iff_ne.mpr this).trans (decide_eq_true hx0).symm

end VG.Proof.Mont.PPC64LE
