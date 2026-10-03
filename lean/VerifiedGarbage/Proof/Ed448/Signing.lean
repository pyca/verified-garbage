import VerifiedGarbage.Proof.Ed448.Scalar

/-!
# Ed448: the signing pipeline

The pieces the code computes, the nonce and the challenge reduced modulo `L`
by `scalarReduce`, `R` by `scalarBase` and `S` by `scalarMulAdd` of any
57-byte encoding of the pruned scalar, make up `Spec.Ed448.sign`
(`sign_pipeline`), given the public key of the private key.
-/

namespace VG.Proof.Ed448

open VG VG.Spec.Ed448

private theorem encodeLE_bytes (n x : Nat) : encodeLE n x = Proof.X25519.leBytes n x := by
  simp only [encodeLE, Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem decodeLE_encodeLE (n x : Nat) : decodeLE (encodeLE n x) = x % 256 ^ n := by
  rw [encodeLE_bytes, decodeLE_eq]
  induction n generalizing x with
  | zero => simp [Proof.X25519.leBytes, Proof.X25519.leNum, Nat.mod_one]
  | succ n ih =>
    rw [Proof.X25519.leBytes_succ, Proof.X25519.leNum, ih, BitVec.toNat_ofNat]
    change x % 256 + 256 * (x / 256 % 256 ^ n) = x % 256 ^ (n + 1)
    rw [Nat.pow_succ', Nat.mod_mul]

theorem decodeLE_scalarReduce (wide : List Byte) : decodeLE (scalarReduce wide) = decodeLE wide % L := by
  rw [scalarReduce, decodeLE_encodeLE, Nat.mod_eq_of_lt]
  have h : L < 256 ^ 57 := by decide +kernel
  exact Nat.lt_trans (Nat.mod_lt _ L_pos) h

/-- The cached key is constrained to the key derived from this very seed. -/
theorem sign_pipeline (seed context message pk sb : List Byte) (hpk : pk = publicKey seed)
    (hs : decodeLE sb = prune (Spec.Sha3.shake256 seed 114)) :
    scalarBase (scalarReduce (hash context ((Spec.Sha3.shake256 seed 114).drop 57 ++ message))) ++
      scalarMulAdd (scalarReduce (hash context ((Spec.Sha3.shake256 seed 114).drop 57 ++ message)))
        (scalarReduce (hash context (scalarBase (scalarReduce (hash context
          ((Spec.Sha3.shake256 seed 114).drop 57 ++ message))) ++ pk ++ message))) sb =
      sign seed context message := by
  rw [scalarMulAdd, decodeLE_scalarReduce, decodeLE_scalarReduce, hs, scalarBase, decodeLE_scalarReduce, hpk]
  rfl

end VG.Proof.Ed448
