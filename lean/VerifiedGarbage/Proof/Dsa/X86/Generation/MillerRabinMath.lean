module
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # Early exits for public parameter-generation primality tests

Once a squaring has established possible primality, further blinded
squarings cannot change the answer. Parameter generation exposes its input
tapes in the timing contract, so its native round may return immediately.
-/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

theorem mrSquarings_true (w a fuel j z : Nat) :
    Spec.RsaKeyGen.mrSquarings w a fuel j z true = true := by
  induction fuel generalizing j z with
  | zero => rfl
  | succ fuel ih =>
    simp [Spec.RsaKeyGen.mrSquarings, ih]

/-- Public rounds stop at the first one or minus one, or after `a - 1`
squarings. This is the same result as the specification's blinded round. -/
def publicMrSquares (w : Nat) : (fuel z : Nat) → Bool
  | 0, _ => false
  | fuel + 1, z =>
    let z' := z * z % w
    if z' == w - 1 then true
    else if z' == 1 then false
    else publicMrSquares w fuel z'

theorem mrSquarings_public {w a fuel j z : Nat} (hj : j ≤ a) (hf : a - j ≤ fuel) :
    Spec.RsaKeyGen.mrSquarings w a fuel j z false = publicMrSquares w (a - j) z := by
  induction fuel generalizing j z with
  | zero =>
    have eq : a - j = 0 := by omega
    rw [eq]; rfl
  | succ fuel ih =>
    by_cases done : j = a
    · subst j
      simp [Spec.RsaKeyGen.mrSquarings, publicMrSquares]
    · have step : a - j = (a - (j + 1)) + 1 := by omega
      rw [Spec.RsaKeyGen.mrSquarings, ite_eq_right (by simp [done]), step, publicMrSquares]
      simp only [Bool.false_or]
      by_cases minus : z * z % w == w - 1
      · simp only [minus, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true]
        exact mrSquarings_true _ _ _ _ _
      · simp only [Bool.eq_false_iff.mpr minus, Bool.not_false, Bool.and_true, Bool.false_eq_true, ite_false]
        by_cases one : z * z % w == 1
        · simp only [one, ite_true]
        · simp only [one]
          exact ih (by omega) (by omega)

def publicMrIteration (w a m b : Nat) : Bool :=
  let z := Spec.Rsa.powMod b m w
  if z == 1 || z == w - 1 then true else publicMrSquares w (a - 1) z

theorem mrIteration_public {w a m b : Nat} (ha : 1 ≤ a) (hab : a ≤ Spec.RsaKeyGen.bitLength w) :
    Spec.RsaKeyGen.mrIteration w a m b = publicMrIteration w a m b := by
  unfold Spec.RsaKeyGen.mrIteration publicMrIteration
  dsimp only
  split
  · rename_i h
    rw [h]; exact mrSquarings_true _ _ _ _ _
  · rename_i h
    have hf : (Spec.Rsa.powMod b m w == 1 || Spec.Rsa.powMod b m w == w - 1) = false :=
      Bool.eq_false_iff.mpr h
    rw [hf]
    exact mrSquarings_public ha (by omega)
end VG.Proof.Dsa.X86.Generation
