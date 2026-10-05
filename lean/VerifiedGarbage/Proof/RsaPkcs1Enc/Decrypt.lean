import VerifiedGarbage.Spec.RsaPkcs1Enc

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection: what it returns

For any private-key operation `rsadp` (`decryptWith`):

* `decryptWith_ok_iff`: decryption returns a message exactly when the
  ciphertext is `k` octets long (and `k ≥ 11`) and `rsadp` returns a result;
  never an error for the padding. `decryptWith_of_invalid`,
  `decryptWith_of_fault`: its errors are those of `rsadp`.
* `decryptWith_of_valid`: for a valid padding, it returns the message of
  `EM`; `implicitDecode_encode`: for `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` with
  `PS` at least 8 nonzero octets, that is `M`.
* `decryptWith_of_not_valid`: otherwise, it returns `alternative k dB C`,
  a function of the private exponent and the ciphertext alone (not of `EM`),
  of at most `k - 11` octets (`alternative_length_le`).
* `decryptWith_encrypt`: if `rsadp` inverts the public-key operation on
  `k`-octet strings, decryption returns the message `encrypt` encrypted.

`Proof/RsaPkcs1Enc/Checked.lean` has the same for `decrypt`, with RSADP
checked against `e` (`Rsa.privateChecked`).
-/

namespace VG.Proof.RsaPkcs1Enc

open Spec.RsaPkcs1Enc
open Spec.Rsa (Outcome)

theorem decryptWith_of_length {rsadp : List Byte → Outcome} {k : Nat} {dB C : List Byte}
    (h : ¬(C.length = k ∧ 11 ≤ k)) : decryptWith rsadp k dB C = .invalid := by
  simp only [decryptWith, h, ite_false]

theorem decryptWith_of_ok {rsadp : List Byte → Outcome} {k : Nat} {dB C EM : List Byte}
    (hC : C.length = k) (hk : 11 ≤ k) (hEM : rsadp C = .ok EM) :
    decryptWith rsadp k dB C = .ok (implicitDecode dB C EM) := by
  simp only [decryptWith, hC, hk, and_self, ite_true, hEM]

theorem decryptWith_of_invalid {rsadp : List Byte → Outcome} {k : Nat} {dB C : List Byte}
    (hEM : rsadp C = .invalid) : decryptWith rsadp k dB C = .invalid := by
  unfold decryptWith
  split <;> simp only [hEM]

theorem decryptWith_of_fault {rsadp : List Byte → Outcome} {k : Nat} {dB C : List Byte}
    (hC : C.length = k) (hk : 11 ≤ k) (hEM : rsadp C = .fault) :
    decryptWith rsadp k dB C = .fault := by
  simp only [decryptWith, hC, hk, and_self, ite_true, hEM]

/-- Decryption returns a message exactly when the ciphertext is `k` octets
long and RSADP returns a result: whatever the padding. -/
theorem decryptWith_ok_iff (rsadp : List Byte → Outcome) (k : Nat) (dB C : List Byte) :
    (∃ M, decryptWith rsadp k dB C = .ok M) ↔
      C.length = k ∧ 11 ≤ k ∧ ∃ EM, rsadp C = .ok EM := by
  by_cases h : C.length = k ∧ 11 ≤ k
  · cases hEM : rsadp C with
    | ok EM => simp [decryptWith_of_ok h.1 h.2 hEM, h]
    | invalid => simp [decryptWith_of_invalid (k := k) (dB := dB) hEM]
    | fault => simp [decryptWith_of_fault (dB := dB) h.1 h.2 hEM]
  · simp only [decryptWith_of_length h, reduceCtorEq, exists_false, false_iff]
    omega

theorem decryptWith_of_valid {rsadp : List Byte → Outcome} {k : Nat}
    {dB C EM : List Byte} (hC : C.length = k) (hk : 11 ≤ k) (hEM : rsadp C = .ok EM)
    (hv : valid EM = true) :
    decryptWith rsadp k dB C = .ok (lastN (msgLength EM) EM) := by
  rw [decryptWith_of_ok hC hk hEM, implicitDecode, hv]
  rfl

/-- For an invalid padding, the message is a function of `k`, `d` and the
ciphertext alone. -/
theorem decryptWith_of_not_valid {rsadp : List Byte → Outcome} {k : Nat}
    {dB C EM : List Byte} (hC : C.length = k) (hk : 11 ≤ k) (hEM : rsadp C = .ok EM)
    (hlen : EM.length = k) (hv : valid EM = false) :
    decryptWith rsadp k dB C = .ok (alternative k dB C) := by
  rw [decryptWith_of_ok hC hk hEM, implicitDecode, hv, hlen]
  rfl

/-- The alternative length is at most `k - 11`. -/
theorem altLength_le (k : Nat) (CL : List Byte) : altLength k CL ≤ k - 11 := by
  unfold altLength
  generalize List.range 128 = is
  suffices ∀ al, al ≤ k - 11 → is.foldl (fun al i =>
      let c := Spec.Rsa.os2ip [CL.getD (2 * i) 0, CL.getD (2 * i + 1) 0] % 2 ^ bitLength (k - 11)
      if c ≤ k - 11 then c else al) al ≤ k - 11 from this 0 (Nat.zero_le _)
  induction is with
  | nil => exact fun _ h => h
  | cons i is ih =>
    intro al hal
    refine ih _ ?_
    dsimp only
    split
    · rename_i hc; exact hc
    · exact hal

theorem lastN_length_le (n : Nat) (xs : List Byte) : (lastN n xs).length ≤ n := by
  simp only [lastN, List.length_drop]
  omega

/-- The message implicit rejection returns is at most `k - 11` octets. -/
theorem alternative_length_le (k : Nat) (dB C : List Byte) :
    (alternative k dB C).length ≤ k - 11 :=
  Nat.le_trans (lastN_length_le _ _) (altLength_le _ _)

/-! ## The message of a valid encoding -/

theorem findIdx?_append_zero (PS M : List Byte) (hPS : PS.all (· != 0) = true) :
    (PS ++ 0 :: M).findIdx? (· == 0) = some PS.length := by
  induction PS with
  | nil => simp [List.findIdx?_cons]
  | cons x PS ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hPS
    rw [List.cons_append, List.findIdx?_cons, ih hPS.2]
    simpa using hPS.1

theorem separator_encode (M PS : List Byte) (hPS : PS.all (· != 0) = true) :
    separator (encode M PS) = some (PS.length + 2) := by
  have h : (encode M PS).drop 2 = PS ++ 0 :: M := by simp [encode]
  rw [separator, h, findIdx?_append_zero PS M hPS]
  rfl

theorem encode_length (M PS : List Byte) : (encode M PS).length = PS.length + M.length + 3 := by
  simp [encode]
  omega

theorem valid_encode (M PS : List Byte) (hPS : PS.all (· != 0) = true) (h8 : 8 ≤ PS.length) :
    valid (encode M PS) = true := by
  simp only [valid, separator_encode M PS hPS]
  simp [encode]
  omega

theorem msgLength_encode (M PS : List Byte) (hPS : PS.all (· != 0) = true) :
    msgLength (encode M PS) = M.length := by
  simp only [msgLength, separator_encode M PS hPS, encode_length]
  omega

theorem lastN_encode (M PS : List Byte) : lastN M.length (encode M PS) = M := by
  have h : encode M PS = ([0x00, 0x02] ++ PS ++ [0x00]) ++ M := by simp [encode]
  rw [lastN, h, List.length_append]
  simp

/-- A valid encoding decodes to its message. -/
theorem implicitDecode_encode (dB C M PS : List Byte) (hPS : PS.all (· != 0) = true)
    (h8 : 8 ≤ PS.length) : implicitDecode dB C (encode M PS) = M := by
  simp only [implicitDecode, valid_encode M PS hPS h8, ite_true, msgLength_encode M PS hPS,
    lastN_encode]

/-! ## Round trip -/

theorem i2osp_length (x n : Nat) : (Spec.Rsa.i2osp x n).length = n := by simp [Spec.Rsa.i2osp]

theorem publicOp_length {nB eB xB C : List Byte} (h : Spec.Rsa.publicOp nB eB xB = some C) :
    C.length = nB.length := by
  dsimp only [Spec.Rsa.publicOp] at h
  split at h
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact i2osp_length _ _
  · cases h

/-- If `rsadp` inverts the public-key operation `Rsa.publicOpChecked nB eB`
on `k`-octet strings, decrypting what `encrypt` gives returns the message. -/
theorem decryptWith_encrypt {nB eB M PS C : List Byte} {rsadp : List Byte → Outcome}
    (hinv : ∀ x c, x.length = nB.length → Spec.Rsa.publicOpChecked nB eB x = some c →
      rsadp c = .ok x)
    (dB : List Byte) (h : encrypt nB eB M PS = some C) :
    decryptWith rsadp nB.length dB C = .ok M := by
  dsimp only [encrypt] at h
  split at h
  · rename_i hc
    obtain ⟨hM, hPSl, hPS⟩ := hc
    have hEM : (encode M PS).length = nB.length := by rw [encode_length]; omega
    have hC : C.length = nB.length := by
      dsimp only [Spec.Rsa.publicOpChecked] at h
      split at h
      · exact publicOp_length h
      · cases h
    rw [decryptWith_of_ok hC (by omega) (hinv _ _ hEM h),
      implicitDecode_encode dB C M PS hPS (by omega)]
  · cases h

end VG.Proof.RsaPkcs1Enc
