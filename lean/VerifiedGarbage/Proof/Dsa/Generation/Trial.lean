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

end VG.Proof.Dsa.Generation
