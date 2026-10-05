import VerifiedGarbage.Proof.RsaPkcs1Sig.Octets
import VerifiedGarbage.Spec.RsaPkcs1Sig

/-!
# RSASSA-PKCS1-v1_5 verification accepts exactly the encoding

* `unpad_eq_some_iff`: BoringSSL's padding check of a `k`-octet `EM` finds
  `T` exactly when `EM` is `0x00 ‖ 0x01 ‖ PS ‖ 0x00 ‖ T` with
  `k - tLen - 3 ≥ 8` octets `0xff` in `PS`: the padding is determined by
  `T` and `k`.
* `verify_eq_verifyRfc`: BoringSSL's verification (check the padding, then
  compare what follows with the `DigestInfo`) is RFC 8017 §8.2.2's
  (encode, then compare).
* `verify_iff`: verification accepts exactly when `sig` is `k` octets, the
  key is valid, `s < n` and `s^e mod n` is the integer of the encoding of
  the given hash value: there is no other accepted `s`, so nothing a lax
  parser of the `DigestInfo` would accept (trailing or hidden octets,
  other lengths, other parameters) is accepted.
* `recover_eq_some_iff`: `recover` returns `H` exactly when `verify`
  accepts `H`.
-/

namespace VG.Proof.RsaPkcs1Sig

open Spec.Rsa Spec.RsaPkcs1Sig

/-! ## The padding -/

/-- The encoded message `0x00 ‖ 0x01 ‖ PS ‖ 0x00 ‖ T`, with `j` octets
`0xff` in `PS`. -/
def padded (j : Nat) (T : List Byte) : List Byte :=
  [0x00, 0x01] ++ List.replicate j 0xff ++ [0x00] ++ T

theorem padded_length (j : Nat) (T : List Byte) : (padded j T).length = j + 3 + T.length := by
  simp [padded]; omega

theorem takeWhile_ff (j : Nat) (T : List Byte) :
    (List.replicate j (0xff : Byte) ++ 0x00 :: T).takeWhile (· == 0xff) = List.replicate j 0xff := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.cons_append, List.takeWhile_cons_of_pos rfl, ih]

theorem dropWhile_ff (j : Nat) (T : List Byte) :
    (List.replicate j (0xff : Byte) ++ 0x00 :: T).dropWhile (· == 0xff) = 0x00 :: T := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.cons_append, List.dropWhile_cons_of_pos rfl, ih]

theorem unpad_padded (j : Nat) (T : List Byte) :
    unpad (padded j T) = if 8 ≤ j then some T else none := by
  have h : padded j T = 0x00 :: 0x01 :: (List.replicate j 0xff ++ 0x00 :: T) := by simp [padded]
  rw [h, unpad]
  simp only [dropWhile_ff, takeWhile_ff, List.length_replicate]
  by_cases hj : 8 ≤ j <;> simp [hj]

theorem eq_padded_of_unpad {em T : List Byte} (h : unpad em = some T) :
    ∃ j, 8 ≤ j ∧ em = padded j T := by
  match em, h with
  | a :: b :: rest, h =>
    simp only [unpad] at h
    split at h
    · rename_i c t hd
      split at h
      · rename_i hc
        obtain ⟨rfl, rfl, rfl, h8⟩ := hc
        cases h
        refine ⟨(rest.takeWhile (· == 0xff)).length, h8, ?_⟩
        have hps : rest.takeWhile (· == 0xff) =
            List.replicate (rest.takeWhile (· == 0xff)).length 0xff := by
          refine List.eq_replicate_iff.2 ⟨rfl, fun x hx => ?_⟩
          exact beq_iff_eq.1 (List.all_eq_true.1 List.all_takeWhile x hx)
        have hr := List.takeWhile_append_dropWhile (p := (· == (0xff : Byte))) (l := rest)
        rw [hd, hps] at hr
        rw [← hr]
        simp [padded]
      · cases h
    · cases h

theorem unpad_eq_some_iff {em T : List Byte} :
    unpad em = some T ↔ T.length + 11 ≤ em.length ∧ em = padded (em.length - T.length - 3) T := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := eq_padded_of_unpad h
    rw [padded_length]
    refine ⟨by omega, ?_⟩
    congr 1
    omega
  · rintro ⟨hl, he⟩
    rw [he, unpad_padded, ite_eq_left (by omega)]

/-! ## The encoding -/

theorem encode_eq_some_iff {h : Hash} {H em : List Byte} {k : Nat} :
    encode h H k = some em ↔
      H.length = h.len ∧ (digestInfo h H).length + 11 ≤ k ∧
        em = padded (k - (digestInfo h H).length - 3) (digestInfo h H) := by
  simp only [encode]
  by_cases hc : H.length ≠ h.len ∨ k < (digestInfo h H).length + 11
  · rw [ite_eq_left hc]
    simp only [reduceCtorEq, false_iff]
    omega
  · rw [ite_eq_right hc, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨by omega, by omega, by simp [padded]⟩
    · rintro ⟨-, -, rfl⟩; simp [padded]

theorem encode_length {h : Hash} {H em : List Byte} {k : Nat} (he : encode h H k = some em) :
    em.length = k := by
  obtain ⟨-, hk, rfl⟩ := encode_eq_some_iff.1 he
  rw [padded_length]; omega

/-! ## Verification -/

theorem publicOp_length {nB eB sig em : List Byte} (h : publicOp nB eB sig = some em) :
    em.length = nB.length := by
  simp only [publicOp, encrypt] at h
  by_cases hv : modulusValid (os2ip nB) nB.length = true
  · by_cases hl : os2ip sig < os2ip nB
    · simp only [hv, hl, ite_true, Option.map_some, Option.some.injEq] at h
      rw [← h]; exact i2osp_length _ _
    · simp [hv, hl] at h
  · simp [hv] at h

theorem publicOpChecked_length {nB eB sig em : List Byte}
    (h : publicOpChecked nB eB sig = some em) : em.length = nB.length := by
  unfold publicOpChecked at h
  split at h
  · exact publicOp_length h
  · cases h

theorem verify_true (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    verify nB eB h H sig = true ↔
      sig.length = nB.length ∧ H.length = h.len ∧
        ∃ em, publicOpChecked nB eB sig = some em ∧ unpad em = some (digestInfo h H) := by
  unfold verify
  by_cases hc : sig.length = nB.length ∧ H.length = h.len
  · rw [ite_eq_left hc]
    cases hp : publicOpChecked nB eB sig <;> simp [hc]
  · rw [ite_eq_right hc]
    simp only [Bool.false_eq_true, false_iff]
    exact fun h' => hc ⟨h'.1, h'.2.1⟩

theorem verifyRfc_true (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    verifyRfc nB eB h H sig = true ↔
      sig.length = nB.length ∧
        ∃ em, publicOpChecked nB eB sig = some em ∧ encode h H nB.length = some em := by
  unfold verifyRfc
  by_cases hc : sig.length = nB.length
  · rw [ite_eq_left hc]
    cases hp : publicOpChecked nB eB sig <;> cases he : encode h H nB.length <;> simp [hc]
    exact eq_comm
  · rw [ite_eq_right hc]
    simp [hc]

/-- For a `k`-octet `EM`, the padding check finds the `DigestInfo` of `H`
(which is `hLen` octets) exactly when `EM` is the encoding of `H`. -/
theorem unpad_iff_encode {h : Hash} {H em : List Byte} {k : Nat} (hem : em.length = k) :
    (H.length = h.len ∧ unpad em = some (digestInfo h H)) ↔ encode h H k = some em := by
  rw [unpad_eq_some_iff, encode_eq_some_iff, hem]

/-- BoringSSL's verification is RFC 8017 §8.2.2's. -/
theorem verify_eq_verifyRfc (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    verify nB eB h H sig = verifyRfc nB eB h H sig := by
  rw [Bool.eq_iff_iff, verify_true, verifyRfc_true]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hH, em, hp, hu⟩
    exact ⟨em, hp, (unpad_iff_encode (publicOpChecked_length hp)).1 ⟨hH, hu⟩⟩
  · rintro ⟨em, hp, he⟩
    have := (unpad_iff_encode (publicOpChecked_length hp)).2 he
    exact ⟨this.1, em, hp, this.2⟩

/-- Verification accepts exactly when `sig` is `k` octets and RSAVP1 of it is
the encoding of `H`. -/
theorem verify_iff_publicOpChecked (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    verify nB eB h H sig = true ↔
      sig.length = nB.length ∧
        ∃ em, encode h H nB.length = some em ∧ publicOpChecked nB eB sig = some em := by
  rw [verify_eq_verifyRfc, verifyRfc_true]
  exact and_congr_right fun _ => exists_congr fun _ => And.comm

/-- Verification accepts exactly when `sig` is `k` octets, the public key is
valid (`modulusValid`, `exponentValid`), `s = OS2IP(sig) < n`, and
`s^e mod n` is the integer of the encoding of `H` (which exists: `H` is
`hLen` octets and `k ≥ tLen + 11`). -/
theorem verify_iff (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    verify nB eB h H sig = true ↔
      sig.length = nB.length ∧ modulusValid (os2ip nB) nB.length = true ∧
        exponentValid (os2ip eB) = true ∧ os2ip sig < os2ip nB ∧
        ∃ em, encode h H nB.length = some em ∧
          powMod (os2ip sig) (os2ip eB) (os2ip nB) = os2ip em := by
  rw [verify_iff_publicOpChecked]
  refine and_congr_right fun _ => ?_
  simp only [publicOpChecked, publicOp, encrypt]
  by_cases he : exponentValid (os2ip eB) = true
  · by_cases hv : modulusValid (os2ip nB) nB.length = true
    · have hn : 0 < os2ip nB := by
        unfold modulusValid at hv
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
        omega
      by_cases hlt : os2ip sig < os2ip nB
      · simp only [he, hv, hlt, ite_true, Option.map_some, Option.some.injEq, true_and]
        refine exists_congr fun em => and_congr_right fun he => ?_
        exact i2osp_eq_iff (Nat.lt_trans (powMod_lt _ _ _ hn) (os2ip_lt nB)) (encode_length he)
      · simp [he, hv, hlt]
    · simp [he, hv]
  · simp [he]

/-! ## Recovery -/

/-- `recover` returns `H` exactly when `verify` accepts `H`. -/
theorem recover_eq_some_iff (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    recover nB eB h sig = some H ↔ verify nB eB h H sig = true := by
  rw [verify_true]
  unfold recover
  by_cases hs : sig.length = nB.length
  · rw [ite_eq_left hs]
    simp only [hs, true_and]
    cases hp : publicOpChecked nB eB sig with
    | none => simp
    | some em =>
      simp only [Option.some.injEq, exists_eq_left']
      cases hu : unpad em with
      | none => simp
      | some t =>
        simp only [digestInfo, Option.some.injEq]
        constructor
        · intro hr
          by_cases hc : t.length = h.prefix.length + h.len ∧ t.take h.prefix.length = h.prefix
          · rw [ite_eq_left hc, Option.some.injEq] at hr
            subst hr
            have ht := List.take_append_drop h.prefix.length t
            rw [hc.2] at ht
            exact ⟨by simp only [List.length_drop]; omega, ht.symm⟩
          · rw [ite_eq_right hc] at hr; cases hr
        · rintro ⟨hH, rfl⟩
          rw [ite_eq_left ⟨by simp [hH], by simp⟩]
          simp
  · rw [ite_eq_right hs]
    simp [hs]

end VG.Proof.RsaPkcs1Sig
