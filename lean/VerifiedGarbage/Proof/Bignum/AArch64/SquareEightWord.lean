module
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Ed25519.Word64

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

def accValue (s : State) : Nat :=
 (s.gpr .x19).toNat + 2 ^ 64 * (s.gpr .x20).toNat + 2 ^ 128 * (s.gpr .x21).toNat

theorem triple_add {r a b c lo hi u v w c1 c2 c3 : Nat}
    (h1 : u + r * c1 = a + lo)
    (h2 : v + r * c2 = b + hi + c1)
    (h3 : w + r * c3 = c + c2) :
    u + r * v + r * r * w + r * r * r * c3 =
      a + r * b + r * r * c + lo + r * hi := by
  grind

/-- A bounded three-word accumulator absorbs a complete 128-bit product.
The bound proves the carry discarded by the final ADC is zero. -/
theorem add_pair_value (a b c lo hi : Word)
    (hbound : a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + lo.toNat +
      2 ^ 64 * hi.toNat < 2 ^ 192) :
    (addCarry a lo false).toNat +
      2 ^ 64 * (addCarry b hi (carryOut a lo false)).toNat +
      2 ^ 128 * (addCarry c 0 (carryOut b hi (carryOut a lo false))).toNat =
        a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + lo.toNat + 2 ^ 64 * hi.toNat := by
  have h1 := addCarry_value a lo false
  have h2 := addCarry_value b hi (carryOut a lo false)
  have h3 := addCarry_value c 0 (carryOut b hi (carryOut a lo false))
  simp only [Bool.toNat_false, Nat.add_zero] at h1
  simp only [show (0 : Word).toNat = 0 from rfl, Nat.add_zero] at h3
  have h := triple_add h1 h2 h3
  have powers : (2 ^ 64 : Nat) * 2 ^ 64 = 2 ^ 128 := by rw [← Nat.pow_add]
  have powers' : (2 ^ 64 : Nat) * 2 ^ 64 * 2 ^ 64 = 2 ^ 192 := by rw [← Nat.pow_add, ← Nat.pow_add]
  rw [powers', powers] at h
  have hc : (carryOut c 0 (carryOut b hi (carryOut a lo false))).toNat = 0 := by
    by_contra hn
    have hp := Nat.mul_le_mul_left (2 ^ 192) (show 1 ≤ (carryOut c 0 (carryOut b hi (carryOut a lo false))).toNat by omega)
    simp only [Nat.mul_one] at hp
    omega
  simpa only [hc, Nat.mul_zero, Nat.add_zero] using h

def addPair (lo hi : Reg) : List Instr :=
 [.adds .x .x19 .x19 lo, .adcs .x .x20 .x20 hi, .adc .x .x21 .x21 .x7]

theorem addPair_ok {s : State} {lo hi : Reg}
    (hhi : hi ≠ .x19) (h7 : s.gpr .x7 = 0)
    (hbound : accValue s + (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat < 2 ^ 192) :
    WP isa (.block (addPair lo hi)) s fun t =>
      (accValue t = accValue s + (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat ∧
        t.mem = s.mem) ∧ Keep [.x19, .x20, .x21] s t := by
  refine WP.keep [.x19, .x20, .x21] ?_ rfl rfl rfl
  unfold addPair accValue
  brun [hhi, h7]
  exact add_pair_value _ _ _ _ _ hbound

end VG.Proof.Bignum.AArch64.SquareEight
