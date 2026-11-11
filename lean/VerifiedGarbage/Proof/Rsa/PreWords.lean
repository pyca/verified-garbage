module

public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA private keys' precomputed values: their parts

`vg_rsa_private_precompute` writes the modulus' values (`publicPrecompute`),
then `R_p² mod p` and `R_q² mod q` (`privatePrecompute`). These lemmas read
each part from `pre`'s words, for the operations given them that use those
parts: the modulus' values are its first `precomputedWords` words
(`privatePrecompute_public`), and the factors' values follow
(`privatePrecompute_primes`).
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG

/-- The first `a` words of `wordsAt`. -/
theorem wordsAt_take (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (Spec.Rsa.wordsAt m p n).take a = Spec.Rsa.wordsAt m p a := by
  unfold Spec.Rsa.wordsAt
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-- `wordsAt` past its first `a` words. -/
theorem wordsAt_drop (m : Mem) (p : Addr) (a n : Nat) :
    (Spec.Rsa.wordsAt m p (a + n)).drop a = Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) n := by
  unfold Spec.Rsa.wordsAt
  rw [← List.map_drop, List.range_add, List.drop_left' (List.length_range), List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add]

theorem toWords_length (x w : Nat) : (Spec.Rsa.toWords x w).length = w := by
  simp [Spec.Rsa.toWords]

/-- The modulus' values are `pre`'s first `2 ⌈k / 8⌉` words. -/
theorem privatePrecompute_public {m : Mem} {pre : Addr} {L : Nat} {nB pB qB : List Byte}
    (h : Spec.Rsa.privatePrecompute nB pB qB = some (Spec.Rsa.wordsAt m pre L)) :
    Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt m pre (Spec.Rsa.precomputedWords nB.length)) := by
  unfold Spec.Rsa.privatePrecompute at h
  split at h
  · cases hp : Spec.Rsa.publicPrecompute nB with
    | none => rw [hp] at h; exact absurd h (by simp)
    | some ws =>
      rw [hp] at h
      have hws : Spec.Rsa.wordsAt m pre L = ws ++ (Spec.Rsa.primeR2 pB ++ Spec.Rsa.primeR2 qB) := by
        simp only [Option.map_some, Option.some.injEq] at h; rw [← h, List.append_assoc]
      have hl : ws.length = Spec.Rsa.precomputedWords nB.length := by
        simp only [Spec.Rsa.publicPrecompute] at hp
        split at hp
        · simp only [Option.some.injEq] at hp
          rw [← hp, List.length_append, toWords_length, toWords_length, Spec.Rsa.precomputedWords]; omega
        · exact absurd hp (by simp)
      have hL : Spec.Rsa.precomputedWords nB.length ≤ L := by
        have := congrArg List.length hws
        simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range, List.length_append] at this
        omega
      rw [← wordsAt_take m pre hL, hws, ← hl, List.take_left]
  · exact absurd h (by simp)

/-- `R_p² mod p` and `R_q² mod q` follow the modulus' values in `pre`. -/
theorem privatePrecompute_primes {m : Mem} {pre : Addr} {nB pB qB : List Byte}
    (h : Spec.Rsa.privatePrecompute nB pB qB = some (Spec.Rsa.wordsAt m pre
      (Spec.Rsa.privatePrecomputedWords nB.length pB.length qB.length))) :
    Spec.Rsa.wordsAt m (pre + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords nB.length))
      (Spec.Rsa.primeWords pB.length) = Spec.Rsa.primeR2 pB ∧
    Spec.Rsa.wordsAt m (pre + BitVec.ofNat 64 (8 * (Spec.Rsa.precomputedWords nB.length +
      Spec.Rsa.primeWords pB.length))) (Spec.Rsa.primeWords qB.length) = Spec.Rsa.primeR2 qB := by
  have hpub := privatePrecompute_public h
  unfold Spec.Rsa.privatePrecompute at h
  split at h
  · rw [hpub] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hpl : (Spec.Rsa.primeR2 pB).length = Spec.Rsa.primeWords pB.length := toWords_length _ _
    have hql : (Spec.Rsa.primeR2 qB).length = Spec.Rsa.primeWords qB.length := toWords_length _ _
    have hw : Spec.Rsa.privatePrecomputedWords nB.length pB.length qB.length =
        Spec.Rsa.precomputedWords nB.length + (Spec.Rsa.primeWords pB.length + Spec.Rsa.primeWords qB.length) := by
      unfold Spec.Rsa.privatePrecomputedWords; omega
    have hd := wordsAt_drop m pre (Spec.Rsa.precomputedWords nB.length)
      (Spec.Rsa.primeWords pB.length + Spec.Rsa.primeWords qB.length)
    rw [← hw, ← h, List.append_assoc, List.drop_left' (by simp [Spec.Rsa.wordsAt])] at hd
    have hd2 := wordsAt_drop m (pre + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords nB.length))
      (Spec.Rsa.primeWords pB.length) (Spec.Rsa.primeWords qB.length)
    rw [← hd, List.drop_left' hpl, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← Nat.mul_add] at hd2
    refine ⟨?_, hd2.symm⟩
    have ht := wordsAt_take m (pre + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords nB.length))
      (Nat.le_add_right (Spec.Rsa.primeWords pB.length) (Spec.Rsa.primeWords qB.length))
    conv at ht => lhs; rw [← hd]; arg 1; rw [← hpl]
    rw [List.take_left] at ht
    exact ht.symm
  · exact absurd h (by simp)

end VG.Proof.Rsa
