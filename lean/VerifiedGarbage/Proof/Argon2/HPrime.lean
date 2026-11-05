module

public import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# Argon2 H′: lengths and the streaming BLAKE2b specification

The length lemmas describe H′'s 32-byte prefixes and final 33–64-byte
hash. `H_stream` restates `Spec.Blake2.blake2b_eq_finalHash` for H.
-/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem wordList_length (xs : List (BitVec 64)) :
    (xs.flatMap Spec.Blake2.wordBytes).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, Spec.Blake2.wordBytes,
      List.length_map, List.length_range, List.length_cons] at *
    omega

theorem H_length (n : Nat) (input : List Byte) (hn : n ≤ 64) : (H n input).length = n := by
  simp only [H, Spec.Blake2.blake2b, Spec.Blake2.blake2, List.length_take,
    wordList_length, Vector.length_toList]
  exact Nat.min_eq_left hn

theorem longHash_length (lastLen r : Nat) (v : List Byte)
    (hn : lastLen ≤ 64) (hv : v.length = 64) :
    (longHash lastLen r v).length = 32 * r + lastLen := by
  induction r generalizing v with
  | zero => simp only [longHash, H_length _ _ hn, Nat.mul_zero, Nat.zero_add]
  | succ r ih =>
    cases r with
    | zero => simp only [longHash, List.length_append, List.length_take,
        hv, H_length _ _ hn]; omega
    | succ r =>
      simp only [longHash, List.length_append, List.length_take, hv]
      rw [ih (H 64 v) (H_length 64 v (by decide))]
      omega

theorem longHash_bounds (n : Nat) (hn : 64 < n) :
    let r := (n + 31) / 32 - 2
    1 ≤ r ∧ 33 ≤ n - 32 * r ∧ n - 32 * r ≤ 64 ∧ 32 * r + (n - 32 * r) = n := by
  dsimp only
  omega

theorem hPrime_length (n : Nat) (input : List Byte) : (hPrime n input).length = n := by
  unfold hPrime
  split
  · exact H_length _ _ (by assumption)
  · rename_i hn
    have hb := longHash_bounds n (by omega)
    rw [longHash_length _ _ _ hb.2.2.1 (H_length 64 _ (by decide))]
    exact hb.2.2.2

/-- The digest after `r` further 64-byte hashes. -/
def chainDigest : Nat → List Byte → List Byte
  | 0, v => v
  | r + 1, v => chainDigest r (H 64 v)

/-- The prefixes emitted by those further hashes. -/
def chainPrefixes : Nat → List Byte → List Byte
  | 0, _ => []
  | r + 1, v => (H 64 v).take 32 ++ chainPrefixes r (H 64 v)

theorem chainDigest_length (r : Nat) (v : List Byte) (hv : v.length = 64) :
    (chainDigest r v).length = 64 := by
  induction r generalizing v with
  | zero => exact hv
  | succ r ih => exact ih _ (H_length _ _ (by decide))

theorem chainPrefixes_length (r : Nat) (v : List Byte) :
    (chainPrefixes r v).length = 32 * r := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    simp only [chainPrefixes, List.length_append, List.length_take, H_length 64 _ (by decide), ih]
    omega

theorem longHash_chain (lastLen r : Nat) (v : List Byte) :
    longHash lastLen (r + 1) v =
      v.take 32 ++ chainPrefixes r v ++ H lastLen (chainDigest r v) := by
  induction r generalizing v with
  | zero => simp only [longHash, chainPrefixes, chainDigest, List.append_nil]
  | succ r ih =>
    rw [longHash, ih]
    simp only [chainPrefixes, chainDigest, List.append_assoc]

theorem H_stream (n : Nat) (m : List Byte) :
    H n m = (Spec.Blake2.finalHash Spec.Blake2.b (Spec.Blake2.init Spec.Blake2.b n 0) m).take n :=
  Spec.Blake2.blake2b_eq_finalHash n [] m (Nat.zero_le _)

end VG.Proof.Argon2
