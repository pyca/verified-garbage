module

public import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
import VerifiedGarbage.Proof.Rsa.RecoverMath

/-! # Bounds and split-exponent facts for the recovery body -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (splitTwos)

def countBits (g : CallGeometry) : Nat := 8 * ((g.args 9).toNat + (g.args 7).toNat)
def exponent (g : CallGeometry) (m : Mem) : Nat := product g m - 1

theorem Inputs.countBounds {g : CallGeometry} {s : State} (h : Inputs g s) :
    0 < countBits g ∧ countBits g ≤ 16384 := by
  have e := h.inputBound 1
  have d := h.inputBound 2
  have pos := h.inputPositive 1
  have upper := h.upper
  change (g.args 7).toNat ≤ 8 * g.n at e
  change (g.args 9).toNat ≤ 8 * g.n at d
  change 0 < (g.args 7).toNat at pos
  unfold countBits
  omega

/-- The exponent's bits fit its words with room for the windows' alignment. -/
theorem Inputs.countWide {g : CallGeometry} {s : State} (h : Inputs g s) :
    countBits g < 32 * g.toGeo.W := by
  have e := h.inputBound 1
  have d := h.inputBound 2
  change (g.args 7).toNat ≤ 8 * g.n at e
  change (g.args 9).toNat ≤ 8 * g.n at d
  simp only [countBits, Geo.W, wide, width]
  change _ < 32 * (2 * (2 * g.n + 2) + 2)
  omega

theorem product_lt (g : CallGeometry) (m : Mem) : product g m < 2 ^ countBits g := by
  have e := inputValue_lt g m 1
  have d := inputValue_lt g m 2
  change inputValue g m 1 < 2 ^ (8 * (g.args 7).toNat) at e
  change inputValue g m 2 < 2 ^ (8 * (g.args 9).toNat) at d
  have bound := Nat.mul_lt_mul'' d e
  rw [← Nat.pow_add] at bound
  simpa only [product, countBits, Nat.mul_add] using bound

theorem exponent_facts {g : CallGeometry} {m : Mem} (go : GoOn (product g m)) :
    2 * (product g m / 2) = exponent g m ∧ 0 < exponent g m ∧ exponent g m % 2 = 0 ∧
    exponent g m < 2 ^ countBits g := by
  have bound := product_lt g m
  unfold GoOn at go
  unfold exponent
  omega

theorem split_facts {g : CallGeometry} {m : Mem} (go : GoOn (product g m)) :
    1 ≤ (splitTwos (exponent g m)).1 ∧ (splitTwos (exponent g m)).1 ≤ countBits g ∧
    (splitTwos (exponent g m)).2 < 2 ^ countBits g := by
  obtain ⟨_, positive, even, bound⟩ := exponent_facts go
  obtain ⟨factor, _⟩ := VG.Proof.Rsa.splitTwos_spec positive
  refine ⟨?_, Nat.le_of_lt (VG.Proof.Rsa.splitTwos_lt positive bound), ?_⟩
  · rw [VG.Proof.Rsa.splitTwos_even (by omega) even]
    omega
  · have le : (splitTwos (exponent g m)).2 ≤ exponent g m := by
      conv => rhs; rw [factor]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega

theorem inputArguments {g : CallGeometry} {s : State} (h : Inputs g s) :
    CallArgument s g.B g.Z 7 (BitVec.ofNat 32 (g.args 7).toNat) ∧
    CallArgument s g.B g.Z 9 (BitVec.ofNat 32 (g.args 9).toNat) := by
  constructor
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.arguments 7 (by decide)
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.arguments 9 (by decide)

end VG.Proof.Rsa.X86.Recover
