module

public import VerifiedGarbage.Spec.Hkdf.Table
public import VerifiedGarbage.Proof.Hmac.Scratch

/-!
# HKDF: the streaming states of a table's hash function

The streaming states `Spec.Hkdf.streamingOf` gives a hash function represent
a message by their bytes alone (`streamingOf_local`), as each instance's
does (`Proof/Hmac/Scratch.lean`): so the postconditions of `vg_hkdf_key`,
and the preconditions of `vg_hkdf_expand`, read the memory only within
`key`.
-/

@[expose] public section

namespace VG.Proof.Hkdf

theorem streamingOf_local {H : Spec.Mgf1.Hash} {S : Spec.Hmac.StreamingHash}
    (h : Spec.Hkdf.streamingOf H = some S) : Proof.Hmac.ReprLocal S := by
  unfold Spec.Hkdf.streamingOf at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first
    | exact Proof.Hmac.md5_local | exact Proof.Hmac.sha1_local | exact Proof.Hmac.sha224_local
    | exact Proof.Hmac.sha256_local | exact Proof.Hmac.sha384_local | exact Proof.Hmac.sha512_local
    | exact Proof.Hmac.sha512_224_local | exact Proof.Hmac.sha512_256_local

end VG.Proof.Hkdf

namespace VG.Proof.Hkdf

open Spec.Hmac (HashFunction hmac)

variable (H : HashFunction) (prk info : List Byte)

/-- HKDF-Expand's `T(k)` (RFC 5869 §2.3): `T(0)` is empty, and
`T(k + 1) = HMAC-Hash(PRK, T(k) ‖ info ‖ (k + 1))`. -/
def tBlock : Nat → List Byte
  | 0 => []
  | k + 1 => hmac H prk (tBlock k ++ info ++ [BitVec.ofNat 8 (k + 1)])

theorem blocks_succ_gen : ∀ n k, Spec.Hkdf.blocks H prk info (n + 1) (tBlock H prk info k) (k + 1) =
    Spec.Hkdf.blocks H prk info n (tBlock H prk info k) (k + 1) ++ tBlock H prk info (k + n + 1)
  | 0, k => by simp [Spec.Hkdf.blocks, tBlock]
  | n + 1, k => by
    have ih := blocks_succ_gen n (k + 1)
    have ht : hmac H prk (tBlock H prk info k ++ info ++ [BitVec.ofNat 8 (k + 1)]) = tBlock H prk info (k + 1) :=
      rfl
    show hmac H prk (tBlock H prk info k ++ info ++ [BitVec.ofNat 8 (k + 1)]) ++
        Spec.Hkdf.blocks H prk info (n + 1) (hmac H prk (tBlock H prk info k ++ info ++ [BitVec.ofNat 8 (k + 1)]))
          (k + 1 + 1) =
      (hmac H prk (tBlock H prk info k ++ info ++ [BitVec.ofNat 8 (k + 1)]) ++
        Spec.Hkdf.blocks H prk info n (hmac H prk (tBlock H prk info k ++ info ++ [BitVec.ofNat 8 (k + 1)]))
          (k + 1 + 1)) ++ tBlock H prk info (k + (n + 1) + 1)
    rw [ht, ih, List.append_assoc, show k + 1 + n + 1 = k + (n + 1) + 1 by omega]

/-- `T(1) ‖ … ‖ T(n + 1)` is `T(1) ‖ … ‖ T(n)`, then `T(n + 1)`. -/
theorem blocks_succ (n : Nat) : Spec.Hkdf.blocks H prk info (n + 1) [] 1 =
    Spec.Hkdf.blocks H prk info n [] 1 ++ tBlock H prk info (n + 1) := by
  have := blocks_succ_gen H prk info n 0
  simpa [tBlock] using this

/-- Each `T(k)` past the first has the hash's length. -/
theorem tBlock_length {D : Nat} (hD : ∀ x, (H.hash x).length = D) (k : Nat) :
    (tBlock H prk info (k + 1)).length = D := by
  simp only [tBlock, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, hD]

theorem blocks_length {D : Nat} (hD : ∀ x, (H.hash x).length = D) :
    ∀ n, (Spec.Hkdf.blocks H prk info n [] 1).length = n * D
  | 0 => by simp [Spec.Hkdf.blocks]
  | n + 1 => by
    rw [blocks_succ, List.length_append, blocks_length hD n, tBlock_length H prk info hD]
    rw [Nat.succ_mul]

/-- Blocks past the first `L` bytes do not change those bytes. -/
theorem blocks_take {D : Nat} (hD : ∀ x, (H.hash x).length = D) {a L : Nat} (hL : L ≤ a * D) :
    ∀ j, (Spec.Hkdf.blocks H prk info (a + j) [] 1).take L = (Spec.Hkdf.blocks H prk info a [] 1).take L
  | 0 => rfl
  | j + 1 => by
    rw [← Nat.add_assoc, blocks_succ, List.take_append_of_le_length (by
        rw [blocks_length H prk info hD]
        exact Nat.le_trans hL (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))),
      blocks_take hD hL j]

end VG.Proof.Hkdf
