module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState
public import VerifiedGarbage.Proof.Dsa.Generation.QCandidate -- shake: keep (proof fields of exposed definitions)

/-! # A shaped q supplies the arithmetic bounds for p construction -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

def seedPlan (P : SearchContextPlan) (T : GenerationTape P.geometry) (len : T.bytes.length = P.geometry.qLen) (seedUsed : BitVec 32) : PSearchPlan := by
  have qw := P.geometry.qWidth
  have pw := P.geometry.width
  let value := Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape (by omega : 2 ≤ 8 * P.geometry.qLen) T.bytes
  have positive : 0 < value := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) shape.2.1
  have width : 8 * P.geometry.qLen + 1 ≤ 32 * (2 * (P.geometry.pLen / 8)) := by
    rcases pw with h | h | h <;> rw [h] <;> omega
  have upper : 2 * value < 2 ^ (8 * P.geometry.qLen + 1) := by
    rw [Nat.pow_succ']
    exact Nat.mul_lt_mul_of_pos_left shape.2.2 (by decide)
  exact ⟨P, T, len, value, positive,
    Nat.lt_of_lt_of_le upper (Nat.pow_le_pow_right (by decide) width), seedUsed⟩
end VG.Proof.Dsa.X86.Generation
