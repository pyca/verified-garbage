import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.X25519.Bytes

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.VerifyBytes`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Bytes`. -/
section

/-! Reuse the shared little-endian memory lemmas. -/

namespace VG.Proof.Ed25519

open VG VG.Spec.Ed25519

theorem decodeLE_eq (xs : List Byte) : decodeLE xs = Proof.X25519.leNum xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [decodeLE, Proof.X25519.leNum, ih]

theorem decodeLE_append (xs ys : List Byte) :
    decodeLE (xs ++ ys) = decodeLE xs + 256 ^ xs.length * decodeLE ys := by
  simp only [VG.Proof.Ed25519.decodeLE_eq, Proof.X25519.leNum_append]

theorem decodeLE_lt (xs : List Byte) : decodeLE xs < 256 ^ xs.length := by
  rw [VG.Proof.Ed25519.decodeLE_eq]; exact Proof.X25519.leNum_lt xs

end VG.Proof.Ed25519

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.VerifyBytes`. -/
section

/-! Split the fixed-width signature at the R/S boundary. -/

namespace VG.Proof.Ed25519

open VG VG.Spec.Ed25519

theorem signatureBytes_split (m : Mem) (p : Addr) :
    bytesAt m p 64 = bytesAt m p 32 ++ bytesAt m (p + BitVec.ofNat 64 32) 32 :=
  Proof.X25519.bytesAt_add m p 32 32

theorem signatureBytes_take (m : Mem) (p : Addr) : (bytesAt m p 64).take 32 = bytesAt m p 32 := by
  have h : (bytesAt m p 32).length = 32 := Proof.X25519.length_bytesAt m p 32
  rw [VG.Proof.Ed25519.signatureBytes_split]
  simpa only [h] using List.take_left (l₁ := bytesAt m p 32) (l₂ := bytesAt m (p + BitVec.ofNat 64 32) 32)

theorem signatureBytes_drop (m : Mem) (p : Addr) :
    (bytesAt m p 64).drop 32 = bytesAt m (p + BitVec.ofNat 64 32) 32 := by
  have h : (bytesAt m p 32).length = 32 := Proof.X25519.length_bytesAt m p 32
  rw [VG.Proof.Ed25519.signatureBytes_split]
  simpa only [h] using List.drop_left (l₁ := bytesAt m p 32) (l₂ := bytesAt m (p + BitVec.ofNat 64 32) 32)

end VG.Proof.Ed25519

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Decode`. -/
section

/-! The length and canonical-coordinate branches of point decoding. -/

namespace VG.Proof.Ed25519

open VG VG.Spec.X25519

theorem toFe_of_lt (n : Nat) (h : n < P) : Proof.X25519.toFe n = (⟨n, h⟩ : Fe) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt h

private theorem bindPoint (o : Option Fe) (y : Fe) :
    (do let x ← o; pure (⟨x, y, 1, x * y⟩ : Spec.Ed25519.Point)) =
      o.map (fun x => (⟨x, y, 1, x * y⟩ : Spec.Ed25519.Point)) := by
  cases o <;> rfl

theorem decodePoint32 (bs : List Byte) (hl : bs.length = 32) :
    Spec.Ed25519.decodePoint bs =
      if Spec.Ed25519.decodeLE bs % 2 ^ 255 < P then
        (Spec.Ed25519.recoverX (Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255))
          (Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1)).map (fun x =>
            (⟨x, Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255), 1,
              x * Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)⟩ : Spec.Ed25519.Point))
      else none := by
  unfold Spec.Ed25519.decodePoint
  simp only [hl, show (32 != 32) = false by decide, Bool.false_eq_true, ite_false]
  by_cases h : Spec.Ed25519.decodeLE bs % 2 ^ 255 < P
  · rw [dite_eq_left h, ite_eq_left h, toFe_of_lt _ h]
    exact bindPoint _ _
  · rw [dite_eq_right h, ite_eq_right h]

end VG.Proof.Ed25519

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Signing`. -/
section

/-! The primitive signing pipeline equals the complete RFC 8032 specification. -/
namespace VG.Proof.Ed25519
open VG VG.Spec.Ed25519

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
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < L)) (by decide : L ≤ 256 ^ 32)

theorem prune_bound (expanded : List Byte) : prune expanded < 256 ^ 32 := by
  unfold prune
  change _ < 2 ^ 256
  exact Nat.or_lt_two_pow
    (Nat.lt_of_le_of_lt Nat.and_le_right (by decide : 2 ^ 254 - 8 < 2 ^ 256))
    (by decide)

theorem bytesAt_encodeLE (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n = encodeLE n (decodeLE (bytesAt m p n)) := by
  rw [encodeLE_bytes, decodeLE_eq]
  change Spec.X25519.bytesAt m p n = Proof.X25519.leBytes n
    (Proof.X25519.leNum (Spec.X25519.bytesAt m p n))
  rw [Proof.X25519.leNum_bytesAt_read, Proof.X25519.bytesAt_leBytes]

/-- The cached key is constrained to the key derived from this very seed. -/
theorem sign_pipeline (seed pk message : List Byte) (hpk : pk = publicKey seed) :
    let expanded := Spec.Sha512.sha512 seed
    let scalar := encodeLE 32 (prune expanded)
    let nonce := scalarReduce (Spec.Sha512.sha512 (expanded.drop 32 ++ message))
    let r := scalarBase nonce
    let challenge := scalarReduce (Spec.Sha512.sha512 (r ++ pk ++ message))
    r ++ scalarMulAdd nonce challenge scalar = sign seed message := by
  dsimp only
  rw [scalarMulAdd, decodeLE_scalarReduce, decodeLE_scalarReduce, decodeLE_encodeLE,
    Nat.mod_eq_of_lt (prune_bound _), scalarBase, decodeLE_scalarReduce, hpk]
  rfl

end VG.Proof.Ed25519

end
