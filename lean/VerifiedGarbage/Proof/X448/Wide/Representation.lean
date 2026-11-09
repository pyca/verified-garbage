module

public import VerifiedGarbage.Proof.X448.Wide.Limbs
public import VerifiedGarbage.Proof.X448.Field
import Batteries.Tactic.Init
import Batteries.Logic

/-!
# Headroom-aware X448 field representation

Untrusted: this is an internal arithmetic contract for an eight-word backend.
A representative has a value modulo p and a separate, explicit coefficient
bound. Weak reduction need not normalize every coefficient below the radix.
The public RFC 7748 contract and existing backend contract are unchanged.
-/

@[expose] public section

namespace VG.Proof.X448.Wide.Representation
open VG.Spec.X448
open VG.Proof.X448 (toFe)

/-- Coefficient headroom, independent of the represented field value. -/
def Within (bound : Nat) (f : Nat → Nat) : Prop := ∀ i < 8, f i < bound

/-- Conservative weak bound, closed under the add/sub contracts below. -/
def weakBound : Nat := radix + 32

/-- Four times p leaves room for weak limbs during nonnegative subtraction. -/
def bias (i : Nat) : Nat := if i = 4 then 4 * radix - 8 else 4 * radix - 4

def difference (f g : Nat → Nat) (i : Nat) : Nat := f i + bias i - g i

theorem bias_val : valN bias 8 = 4 * P := by decide +kernel

theorem bias_ge (i : Nat) : weakBound ≤ bias i := by
  simp only [bias]
  split <;> decide +kernel

theorem difference_val {f g : Nat → Nat} (hg : Within weakBound g) :
    valN (difference f g) 8 + valN g 8 = valN f 8 + 4 * P := by
  rw [← valN_add]
  have eq : valN (fun i => difference f g i + g i) 8 =
      valN (fun i => f i + bias i) 8 := by
    apply valN_congr
    intro i hi
    have h := hg i hi
    have b := bias_ge i
    simp only [difference]
    omega
  rw [eq, valN_add, bias_val]

/-- The second serial carry pass has at most one carry-out. -/
theorem second_carry {f : Nat → Nat} (h : Within (2 ^ 118) f) :
    carry (folded f) 8 ≤ 1 := by
  have c0 := carry_bound h
  have v0 := valN_lt (n := 8) (fun i _ => digit_lt f i)
  have e1 := pass_eq (folded f) 8
  rw [folded_val] at e1
  change valN (digit f) 8 < full at v0
  change valN (digit (folded f)) 8 + full * carry (folded f) 8 = _ at e1
  have small : (half + 1) * (2 ^ 63 + 1) < full := by decide +kernel
  by_contra hc
  have hb := Nat.mul_le_mul_left (half + 1) (Nat.le_of_lt c0)
  have hp := Nat.mul_le_mul_left full (show 2 ≤ carry (folded f) 8 from by omega)
  omega

/-- Two carry passes and folds suffice for a weak field representative. -/
theorem twice_weak {f : Nat → Nat} (h : Within (2 ^ 118) f) :
    Within weakBound (folded (folded f)) := by
  have hc := second_carry h
  intro i _
  have hd := digit_lt (folded f) i
  simp only [folded, weakBound]
  split <;> omega

theorem twice_mod (f : Nat → Nat) :
    valN (folded (folded f)) 8 % P = valN f 8 % P := by
  rw [folded_mod, folded_mod]

end VG.Proof.X448.Wide.Representation
