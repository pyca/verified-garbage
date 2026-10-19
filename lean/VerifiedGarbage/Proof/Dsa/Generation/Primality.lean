module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.BitLengthBounds

/-! # DSA's policy around the shared RSA Miller–Rabin loop -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

/-- Subtracting one from an odd candidate preserves its bit length. -/
theorem predecessor_bits {n w : Nat} (hn : 2 ≤ n) (ho : w % 2 = 1)
    (hb : Spec.Dsa.bitLength w = n) : Spec.RsaKeyGen.bitLength (w - 1) = n := by
  obtain ⟨hlo, hhi⟩ := (bitLength_iff_bounds (by omega)).mp hb
  have he : 2 ^ (n - 1) % 2 = 0 := by
    rw [show n - 1 = n - 2 + 1 by omega, Nat.pow_succ, Nat.mul_mod]
    simp
  have hneq : w ≠ 2 ^ (n - 1) := by intro h; rw [h, he] at ho; contradiction
  change Spec.Dsa.bitLength (w - 1) = n
  exact (bitLength_iff_bounds (by omega)).mpr ⟨by omega, by omega⟩

/-- The sampler must consume 24 bytes for a 160-bit candidate, although
only its low 160 bits participate in the witness. Other supported widths
consume exactly their byte width. -/
theorem witness_width {n w : Nat} (hn : 2 ≤ n) (ho : w % 2 = 1)
    (hb : Spec.Dsa.bitLength w = n) :
    Spec.RsaKeyGen.witnessBytes w = 8 * ((n + 63) / 64) := by
  rw [Spec.RsaKeyGen.witnessBytes, predecessor_bits hn ho hb]

/-- The small-value cases are unreachable for a shaped DSA candidate;
trial division precedes exactly RSA's blinded witness loop with DSA's
round count. Tape consumption remains part of the returned result. -/
theorem probablePrime_large {w : Nat} (hw : 3 < w) (ho : w % 2 = 1)
    (rand : Spec.RsaKeyGen.Rand) :
    Spec.Dsa.probablePrime w rand =
      if Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength w) w then some (false, rand)
      else Spec.RsaKeyGen.loop
        (Spec.RsaKeyGen.mrStep w (Spec.Dsa.primeChecks (Spec.Dsa.bitLength w))
          (Spec.Rsa.splitTwos (w - 1)).1 (Spec.Rsa.splitTwos (w - 1)).2) (1, 0) rand := by
  simp only [Spec.Dsa.probablePrime, show ¬ w ≤ 1 by omega, ite_false, ho,
    show ¬ (1 : Nat) = 0 by decide, show (w == 3) = false from beq_eq_false_iff_ne.mpr (by omega),
    Bool.false_eq_true]

end VG.Proof.Dsa.Generation
