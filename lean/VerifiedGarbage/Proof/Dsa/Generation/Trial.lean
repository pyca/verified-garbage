module

public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # DSA's trial-division policy with a padded Montgomery workspace -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

theorem trialAny_dsa {w c bits : Nat} (hc : 8161 < c)
    (hpolicy : 1024 < bits ↔ 16 < w) :
    VG.Proof.RsaKeyGen.trialAny (if 17 ≤ w then 256 else 128) c =
      Spec.RsaKeyGen.obviouslyComposite bits c := by
  rw [VG.Proof.RsaKeyGen.trialAny_eq hc]
  have hp : Spec.RsaKeyGen.trialPrimes (64 * w) = Spec.RsaKeyGen.trialPrimes bits := by
    simp only [Spec.RsaKeyGen.trialPrimes]
    have he : 1024 < 64 * w ↔ 1024 < bits := by omega
    simp only [he]
  simp only [Spec.RsaKeyGen.obviouslyComposite, hp]

/-- Both subgroup widths use four limbs; larger candidates use their
natural width. Padding does not change which small primes are tested. -/
theorem trial_policy {bits : Nat}
    (hbits : bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072) :
    1024 < bits ↔ 16 < max 4 ((bits + 63) / 64) := by
  rcases hbits with h | h | h | h | h <;> subst bits <;> decide

/-- Extend the low-word residue after consuming another candidate word. -/
theorem trial_word_step {s acc next x V j : Nat}
    (step : next * 2 ^ 32 % s = (x + acc) % s)
    (previous : acc * 2 ^ (32 * j) % s = V % s) :
    next * 2 ^ (32 * (j + 1)) % s = (V + 2 ^ (32 * j) * x) % s := by
  have power : next * 2 ^ (32 * (j + 1)) = next * 2 ^ 32 * 2 ^ (32 * j) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rw [power, ← Nat.mod_mul_mod, step, Nat.mod_mul_mod, Nat.add_mul,
    Nat.add_mod, previous, ← Nat.add_mod, Nat.add_comm, Nat.mul_comm x]

end VG.Proof.Dsa.Generation
