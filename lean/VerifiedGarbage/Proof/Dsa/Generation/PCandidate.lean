module

public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Dsa.Digest

/-! ### `Dsa.Generation.Contributions`, which this module and modules that import it used -/

section

/-! ### `Dsa.Generation.PEncoding`, which this module and modules that import it used -/

section

/-! # Assemble the hash contributions for a DSA p candidate

Hashes are stored most significant contribution first. The shared shaper
then keeps the requested low bits and sets the top bit. Its low-bit write
does not change the following even-modulus reduction.
-/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

/-- Joining a high radix digit to a bounded low part commutes with cutting
the high digit. This is the truncation of p's final hash contribution. -/
theorem radix_join_mod {lo base : Nat} (hlo : lo < base) (hi cut : Nat) :
    (lo + hi * base) % (base * cut) = lo + (hi % cut) * base := by
  rw [Nat.mod_mul]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo, Nat.add_mul_div_right _ _ (by omega_using [hlo]),
    Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [Nat.mul_comm]

/-- Appending a digest at the most significant end appends a radix digit. -/
theorem prepend_digest (digest low : List Byte) :
    Spec.Dsa.decodeBE (digest ++ low) =
      Spec.Dsa.decodeBE low + Spec.Dsa.decodeBE digest * 256 ^ low.length := by
  rw [decodeBE_append, Nat.add_comm]

end VG.Proof.Dsa.Generation

end

end

/-! # Radix bounds for the accumulated p-candidate hash contributions -/

@[expose] public section
namespace VG.Proof.Dsa.Generation

def contributions (n : Nat) (v : Nat → Nat) (k : Nat) : Nat :=
  (List.range k).foldl (fun a j => a + v j * 2 ^ (j * n)) 0

theorem contributions_zero (n : Nat) (v : Nat → Nat) : contributions n v 0 = 0 := rfl

theorem contributions_succ (n : Nat) (v : Nat → Nat) (k : Nat) :
    contributions n v (k + 1) = contributions n v k + v k * 2 ^ (k * n) := by
  simp only [contributions, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- k complete n-bit hash values occupy strictly fewer than k*n bits plus
one, including when the most significant digest begins with zeroes. -/
theorem contributions_lt (n : Nat) (v : Nat → Nat) (k : Nat)
    (hv : ∀ j < k, v j < 2 ^ n) : contributions n v k < 2 ^ (k * n) := by
  induction k with
  | zero => simp [contributions_zero]
  | succ k ih =>
    have hlo := ih (fun j hj => hv j (by omega_using [hj]))
    have hhi := hv k (by omega_using [])
    have hmul := Nat.mul_le_mul_right (2 ^ (k * n)) (show v k + 1 ≤ 2 ^ n by omega_using [hhi])
    rw [Nat.add_mul, Nat.one_mul] at hmul
    rw [contributions_succ, Nat.add_mul, Nat.one_mul, Nat.pow_add]
    have hcomm : 2 ^ (k * n) * 2 ^ n = 2 ^ n * 2 ^ (k * n) := Nat.mul_comm _ _
    omega_using [hlo, hmul, hcomm]

/-- The range fold can change its function outside the visited indices. -/
theorem contribution_fold_congr (xs : List Nat) (f g : Nat → Nat)
    (he : ∀ j ∈ xs, f j = g j) (acc : Nat) :
    xs.foldl (fun a j => a + f j) acc = xs.foldl (fun a j => a + g j) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons j xs ih =>
    simp only [List.foldl_cons]
    rw [he j (by simp)]
    exact ih (fun k hk => he k (List.mem_cons_of_mem j hk)) _

/-- The specification truncates only the last contribution. This equals
truncating the complete radix assembly at its final partial digit. -/
theorem contributions_cut (n b count : Nat) (v : Nat → Nat)
    (hv : ∀ j < count, v j < 2 ^ n) :
    (List.range (count + 1)).foldl (fun a j =>
      a + (if j == count then v j % 2 ^ b else v j) * 2 ^ (j * n)) 0 =
        contributions n v (count + 1) % (2 ^ (count * n) * 2 ^ b) := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [beq_self_eq_true, ite_true]
  have hp : (List.range count).foldl (fun a j =>
      a + (if j == count then v j % 2 ^ b else v j) * 2 ^ (j * n)) 0 = contributions n v count := by
    apply contribution_fold_congr
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [beq_eq_false_iff_ne.mpr (by omega_using [hj] : j ≠ count), Bool.false_eq_true, ite_false]
  rw [hp, contributions_succ, radix_join_mod (contributions_lt n v count hv)]

end VG.Proof.Dsa.Generation

end

end

/-! # The shared native shaper and divider implement DSA's p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

/-- Numeric value of one hash contribution, before truncation. -/
def pDigest (n : Nat) (seed : List Byte) (offset j : Nat) : Nat :=
  Spec.Dsa.decodeBE (Spec.Dsa.seedHash n (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + offset + j)))

theorem digest_value_lt {n : Nat} (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash n bs).length = n)
    (seed : List Byte) (offset j : Nat) : pDigest n seed offset j < 2 ^ n := by
  have h := decodeBE_lt (Spec.Dsa.seedHash n (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + offset + j)))
  rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul, hlen] at h
  exact h

/-- The p search can concatenate whole digests, shape the low L bits with
the existing routine, and divide by 2*q. This is exactly the reviewed DSA
formula, including the final partial digest and low-bit adjustment. -/
theorem pCandidate_shaped {l n : Nat} (hl : 2 ≤ l)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash n bs).length = n)
    (q : Nat) (seed : List Byte) (offset : Nat) :
    Spec.Dsa.pCandidate l n q seed offset =
      let x := Spec.Ffdh.candidateOf l (contributions n (pDigest n seed offset) ((l - 1) / n + 1))
      x + 1 - x % (2 * q) := by
  have hpow : 2 ^ (((l - 1) / n) * n) * 2 ^ ((l - 1) % n) = 2 ^ (l - 1) := by
    rw [← Nat.pow_add, Nat.mul_comm ((l - 1) / n) n, Nat.div_add_mod]
  have hv : ∀ j < (l - 1) / n, pDigest n seed offset j < 2 ^ n :=
    fun j _ => digest_value_lt hlen seed offset j
  have hcut := contributions_cut n ((l - 1) % n) ((l - 1) / n) (pDigest n seed offset) hv
  rw [hpow] at hcut
  dsimp only [Spec.Dsa.pCandidate]
  dsimp only [pDigest] at hcut
  rw [hcut, VG.Proof.Ffdh.ParameterCandidate.candidate_low_high (by omega_using [hl]), pReduction_orOne]

/-- Taking only the bytes needed for the candidate before shaping is
identical to shaping the full radix assembly. -/
theorem candidateOf_mod_width {l width : Nat} (hl : 1 ≤ l) (hw : l ≤ width) (x : Nat) :
    Spec.Ffdh.candidateOf l (x % 2 ^ width) = Spec.Ffdh.candidateOf l x := by
  rw [VG.Proof.Ffdh.ParameterCandidate.candidate_low_high hl,
    VG.Proof.Ffdh.ParameterCandidate.candidate_low_high hl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using [hw]))]

end VG.Proof.Dsa.Generation
