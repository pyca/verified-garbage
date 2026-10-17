module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Divstep.Iter
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Ed25519 and X25519 on AArch64: the inversion by divsteps is sound modulo `p = 2²⁵⁵ - 19`

Untrusted: everything here is checked by Lean. After 590 divsteps from
`(1, p, x)`, `g = 0` and `|f| = gcd(p, x)` (`divsteps_590`), which is `1` for
`0 < x < p` as `p` is prime (`Ed25519.prime_field`); so `x u ≡ f = ±1`, and
`±u` is `x⁻¹ = x^(p - 2)`. This module alone imports the algebra that takes.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG.Spec.X25519 VG.Proof.Divstep VG.Proof.Ed25519.AArch64.Inv

theorem toZ_toFe (n : Nat) : VG.Proof.Ed25519.toZ (VG.Proof.X25519.toFe n) = (n : ZMod P) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast]
  rfl

theorem sound_eq {x U R : Nat} (hx : x < P)
    (hcu : 2 ^ 590 * (dsI x 10).2.1 ≡ x * 2 ^ 590 * U [ZMOD P])
    (hz : x = 0 → (U : Int) ≡ 0 [ZMOD P])
    (hR : (R : Int) % P = (if (dsI x 10).2.1 < 0 then -(U : Int) else U) % P) :
    VG.Proof.X25519.toFe R = VG.Proof.X25519.invert (VG.Proof.X25519.toFe x) := by
  rw [VG.Proof.X25519.invert_eq, ← VG.Proof.Ed25519.toZ_inj, VG.Proof.Ed25519.toZ_pow, toZ_toFe,
    toZ_toFe]
  have hRz := (ZMod.intCast_eq_intCast_iff' _ _ _).2 hR
  by_cases h0 : x = 0
  · have hU := (ZMod.intCast_eq_intCast_iff _ _ _).2 (hz h0)
    push_cast at hU hRz
    rw [h0]
    simp only [Nat.cast_zero]
    rw [zero_pow (by simp [P]), hRz]
    split <;> simp [hU]
  · -- 590 divsteps end with `g = 0` and `f = ±1`.
    have hdone := divsteps_590 (f := (P : Int)) (g := (x : Int)) P_odd (by positivity)
      (by exact_mod_cast hx.le) (by rw [P_val]; norm_num) (n := 590) le_rfl
    have hcop : Int.gcd (P : Int) (x : Int) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_of_lt_prime h0 hx VG.Proof.Ed25519.prime_field
    have hs : dsI x 10 = divsteps 590 (1, (P : Int), (x : Int)) := rfl
    rw [hs] at hcu hRz
    generalize (divsteps 590 (1, (P : Int), (x : Int))).2.1 = f at hdone hcu hRz
    rw [hcop] at hdone
    have hf : f = 1 ∨ f = -1 := by omega
    have hv := v0_spec.trans (by decide : (1 : Int) = 1 % P)
    generalize (2 : Int) ^ 590 = Ki at hcu hv
    have hc := (ZMod.intCast_eq_intCast_iff _ _ _).2 hcu
    have k := (ZMod.intCast_eq_intCast_iff' _ _ _).2 hv
    push_cast at hc k
    generalize (Ki : ZMod P) = K at hc k
    -- `f = x U`
    have hfu : (f : ZMod P) = x * U := by
      calc (f : ZMod P) = (f : ZMod P) * (K * Impl.Ed25519.AArch64.Divstep.v0) := by rw [k, mul_one]
        _ = K * f * Impl.Ed25519.AArch64.Divstep.v0 := by ring
        _ = x * K * U * Impl.Ed25519.AArch64.Divstep.v0 := by rw [hc]
        _ = x * U * (K * Impl.Ed25519.AArch64.Divstep.v0) := by ring
        _ = x * U := by rw [k, mul_one]
    -- `x R = 1`
    have hxr : (x : ZMod P) * R = 1 := by
      rcases hf with rfl | rfl
      · simp only [show ¬ (1 : Int) < 0 by decide, ↓reduceIte] at hRz
        push_cast at hRz hfu
        rw [hRz, ← hfu]
      · simp only [show (-1 : Int) < 0 by decide, ↓reduceIte] at hRz
        push_cast at hRz hfu
        rw [hRz, mul_neg, ← hfu, neg_neg]
    have hX : (x : ZMod P) ≠ 0 := fun h => by rw [h, zero_mul] at hxr; exact zero_ne_one hxr
    calc (R : ZMod P) = (R : ZMod P) * x * (x : ZMod P) ^ (P - 2) :=
          (VG.Proof.Ed25519.mul_pow_inv hX _).symm
      _ = x * R * (x : ZMod P) ^ (P - 2) := by ring
      _ = (x : ZMod P) ^ (P - 2) := by rw [hxr, one_mul]

instance sound : Sound := ⟨sound_eq⟩

end VG.Proof.Ed25519.AArch64.Divstep
