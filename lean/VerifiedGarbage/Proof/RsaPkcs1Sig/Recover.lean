import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Spec.RsaPkcs1Sig

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.Octets`. -/
section

/-!
# OS2IP and I2OSP are inverse

For the octet strings of a fixed length `k` and the integers below
`256^k`: `i2osp_os2ip` and `os2ip_i2osp`, so `i2osp x k = em` exactly when
`x = os2ip em` (`i2osp_eq_iff`). And `powMod` is below its modulus.
-/

namespace VG.Proof.RsaPkcs1Sig

open Spec.Rsa

/-- Induction on octet strings from their last octet. -/
theorem snoc_induction {P : List Byte → Prop} (nil : P [])
    (snoc : ∀ bs b, P bs → P (bs ++ [b])) (bs : List Byte) : P bs := by
  have h : ∀ l : List Byte, P l.reverse := by
    intro l
    induction l with
    | nil => exact nil
    | cons b l ih => rw [List.reverse_cons]; exact snoc _ _ ih
  simpa using h bs.reverse

theorem os2ip_append_singleton (bs : List Byte) (b : Byte) :
    os2ip (bs ++ [b]) = 256 * os2ip bs + b.toNat := by
  simp [os2ip, List.foldl_append]

theorem i2osp_length (x k : Nat) : (i2osp x k).length = k := by simp [i2osp]

theorem i2osp_succ (x k : Nat) : i2osp x (k + 1) = i2osp (x / 256) k ++ [BitVec.ofNat 8 x] := by
  unfold i2osp
  rw [List.range_succ, List.map_append]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi : i < k := List.mem_range.1 hi
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    congr 3
    omega
  · simp

theorem os2ip_lt (bs : List Byte) : os2ip bs < 256 ^ bs.length := by
  induction bs using VG.Proof.RsaPkcs1Sig.snoc_induction with
  | nil => decide
  | snoc bs b ih =>
    rw [VG.Proof.RsaPkcs1Sig.os2ip_append_singleton, List.length_append, List.length_singleton, Nat.pow_succ]
    have := b.isLt
    omega

theorem i2osp_os2ip (bs : List Byte) : i2osp (os2ip bs) bs.length = bs := by
  induction bs using VG.Proof.RsaPkcs1Sig.snoc_induction with
  | nil => rfl
  | snoc bs b ih =>
    have hb := b.isLt
    rw [List.length_append, List.length_singleton, VG.Proof.RsaPkcs1Sig.i2osp_succ, VG.Proof.RsaPkcs1Sig.os2ip_append_singleton,
      show (256 * os2ip bs + b.toNat) / 256 = os2ip bs by omega, ih]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

theorem os2ip_i2osp (x k : Nat) (hx : x < 256 ^ k) : os2ip (i2osp x k) = x := by
  induction k generalizing x with
  | zero => simp [i2osp, os2ip]; omega
  | succ k ih =>
    rw [VG.Proof.RsaPkcs1Sig.i2osp_succ, VG.Proof.RsaPkcs1Sig.os2ip_append_singleton, ih (x / 256) (by rw [Nat.pow_succ] at hx; omega),
      BitVec.toNat_ofNat]
    omega

theorem i2osp_eq_iff {x k : Nat} {em : List Byte} (hx : x < 256 ^ k) (hem : em.length = k) :
    i2osp x k = em ↔ x = os2ip em := by
  constructor
  · rintro rfl; exact (VG.Proof.RsaPkcs1Sig.os2ip_i2osp x k hx).symm
  · rintro rfl; rw [← hem]; exact VG.Proof.RsaPkcs1Sig.i2osp_os2ip em

theorem powMod_lt (a e m : Nat) (hm : 0 < m) : powMod a e m < m := by
  unfold powMod
  split
  · exact Nat.mod_lt _ hm
  · dsimp only
    split <;> exact Nat.mod_lt _ hm

end VG.Proof.RsaPkcs1Sig

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.Verify`. -/
section

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

theorem padded_length (j : Nat) (T : List Byte) : (VG.Proof.RsaPkcs1Sig.padded j T).length = j + 3 + T.length := by
  simp [VG.Proof.RsaPkcs1Sig.padded]; omega

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
    unpad (VG.Proof.RsaPkcs1Sig.padded j T) = if 8 ≤ j then some T else none := by
  have h : VG.Proof.RsaPkcs1Sig.padded j T = 0x00 :: 0x01 :: (List.replicate j 0xff ++ 0x00 :: T) := by simp [VG.Proof.RsaPkcs1Sig.padded]
  rw [h, unpad]
  simp only [VG.Proof.RsaPkcs1Sig.dropWhile_ff, VG.Proof.RsaPkcs1Sig.takeWhile_ff, List.length_replicate]
  by_cases hj : 8 ≤ j <;> simp [hj]

theorem eq_padded_of_unpad {em T : List Byte} (h : unpad em = some T) :
    ∃ j, 8 ≤ j ∧ em = VG.Proof.RsaPkcs1Sig.padded j T := by
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
        simp [VG.Proof.RsaPkcs1Sig.padded]
      · cases h
    · cases h

theorem unpad_eq_some_iff {em T : List Byte} :
    unpad em = some T ↔ T.length + 11 ≤ em.length ∧ em = VG.Proof.RsaPkcs1Sig.padded (em.length - T.length - 3) T := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := VG.Proof.RsaPkcs1Sig.eq_padded_of_unpad h
    rw [VG.Proof.RsaPkcs1Sig.padded_length]
    refine ⟨by omega, ?_⟩
    congr 1
    omega
  · rintro ⟨hl, he⟩
    rw [he, VG.Proof.RsaPkcs1Sig.unpad_padded, ite_eq_left (by omega)]

/-! ## The encoding -/

theorem encode_eq_some_iff {h : Hash} {H em : List Byte} {k : Nat} :
    encode h H k = some em ↔
      H.length = h.len ∧ (digestInfo h H).length + 11 ≤ k ∧
        em = VG.Proof.RsaPkcs1Sig.padded (k - (digestInfo h H).length - 3) (digestInfo h H) := by
  simp only [encode]
  by_cases hc : H.length ≠ h.len ∨ k < (digestInfo h H).length + 11
  · rw [ite_eq_left hc]
    simp only [reduceCtorEq, false_iff]
    omega
  · rw [ite_eq_right hc, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨by omega, by omega, by simp [VG.Proof.RsaPkcs1Sig.padded]⟩
    · rintro ⟨-, -, rfl⟩; simp [VG.Proof.RsaPkcs1Sig.padded]

theorem encode_length {h : Hash} {H em : List Byte} {k : Nat} (he : encode h H k = some em) :
    em.length = k := by
  obtain ⟨-, hk, rfl⟩ := encode_eq_some_iff.1 he
  rw [VG.Proof.RsaPkcs1Sig.padded_length]; omega

/-! ## Verification -/

theorem publicOp_length {nB eB sig em : List Byte} (h : publicOp nB eB sig = some em) :
    em.length = nB.length := by
  simp only [publicOp, encrypt] at h
  by_cases hv : modulusValid (os2ip nB) nB.length = true
  · by_cases hl : os2ip sig < os2ip nB
    · simp only [hv, hl, ite_true, Option.map_some, Option.some.injEq] at h
      rw [← h]; exact VG.Proof.RsaPkcs1Sig.i2osp_length _ _
    · simp [hv, hl] at h
  · simp [hv] at h

theorem publicOpChecked_length {nB eB sig em : List Byte}
    (h : publicOpChecked nB eB sig = some em) : em.length = nB.length := by
  unfold publicOpChecked at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.publicOp_length h
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
  rw [VG.Proof.RsaPkcs1Sig.unpad_eq_some_iff, VG.Proof.RsaPkcs1Sig.encode_eq_some_iff, hem]

/-- BoringSSL's verification is RFC 8017 §8.2.2's. -/
theorem verify_eq_verifyRfc (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    verify nB eB h H sig = verifyRfc nB eB h H sig := by
  rw [Bool.eq_iff_iff, VG.Proof.RsaPkcs1Sig.verify_true, VG.Proof.RsaPkcs1Sig.verifyRfc_true]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hH, em, hp, hu⟩
    exact ⟨em, hp, (VG.Proof.RsaPkcs1Sig.unpad_iff_encode (VG.Proof.RsaPkcs1Sig.publicOpChecked_length hp)).1 ⟨hH, hu⟩⟩
  · rintro ⟨em, hp, he⟩
    have := (VG.Proof.RsaPkcs1Sig.unpad_iff_encode (VG.Proof.RsaPkcs1Sig.publicOpChecked_length hp)).2 he
    exact ⟨this.1, em, hp, this.2⟩

/-- Verification accepts exactly when `sig` is `k` octets and RSAVP1 of it is
the encoding of `H`. -/
theorem verify_iff_publicOpChecked (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    verify nB eB h H sig = true ↔
      sig.length = nB.length ∧
        ∃ em, encode h H nB.length = some em ∧ publicOpChecked nB eB sig = some em := by
  rw [VG.Proof.RsaPkcs1Sig.verify_eq_verifyRfc, VG.Proof.RsaPkcs1Sig.verifyRfc_true]
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
  rw [VG.Proof.RsaPkcs1Sig.verify_iff_publicOpChecked]
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
        exact VG.Proof.RsaPkcs1Sig.i2osp_eq_iff (Nat.lt_trans (VG.Proof.RsaPkcs1Sig.powMod_lt _ _ _ hn) (VG.Proof.RsaPkcs1Sig.os2ip_lt nB)) (VG.Proof.RsaPkcs1Sig.encode_length he)
      · simp [he, hv, hlt]
    · simp [he, hv]
  · simp [he]

/-! ## Recovery -/

/-- `recover` returns `H` exactly when `verify` accepts `H`. -/
theorem recover_eq_some_iff (nB eB : List Byte) (h : Hash) (H sig : List Byte) :
    recover nB eB h sig = some H ↔ verify nB eB h H sig = true := by
  rw [VG.Proof.RsaPkcs1Sig.verify_true]
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.Recover`. -/
section

/-!
# RSASSA-PKCS1-v1_5 recovery by encoding

`recover_eq_recoverEnc`: the hash value a signature signs is the last
`hLen` octets of RSAVP1 of it, `EM`, if their encoding is `EM`, as OpenSSL's
`ossl_rsa_verify` with `rm` computes it: so an implementation can recover by
encoding those octets and comparing, with the encoding verification uses.
-/

namespace VG.Proof.RsaPkcs1Sig

open Spec.Rsa Spec.RsaPkcs1Sig

/-- The last `hLen` octets of `EM`, if their encoding is `EM`. -/
def recoverEnc (nB eB : List Byte) (h : Hash) (sig : List Byte) : Option (List Byte) :=
  if sig.length = nB.length then
    match publicOpChecked nB eB sig with
    | some em =>
      if encode h (em.drop (nB.length - h.len)) nB.length = some em then
        some (em.drop (nB.length - h.len))
      else none
    | none => none
  else none

/-- An encoding of `H` ends with `H`. -/
theorem drop_of_encode {h : Hash} {H em : List Byte} {k : Nat} (he : encode h H k = some em) :
    em.drop (k - h.len) = H := by
  have hk := VG.Proof.RsaPkcs1Sig.encode_length he
  obtain ⟨hH, -, rfl⟩ := encode_eq_some_iff.1 he
  rw [show VG.Proof.RsaPkcs1Sig.padded (k - (digestInfo h H).length - 3) (digestInfo h H) =
      ([0x00, 0x01] ++ List.replicate (k - (digestInfo h H).length - 3) 0xff ++ [0x00] ++ h.prefix) ++ H by
    simp [VG.Proof.RsaPkcs1Sig.padded, digestInfo]] at hk ⊢
  rw [List.drop_left']
  rw [List.length_append] at hk
  omega

theorem recover_eq_recoverEnc (nB eB : List Byte) (h : Hash) (sig : List Byte) :
    recover nB eB h sig = VG.Proof.RsaPkcs1Sig.recoverEnc nB eB h sig := by
  apply Option.ext
  intro H
  rw [VG.Proof.RsaPkcs1Sig.recover_eq_some_iff, VG.Proof.RsaPkcs1Sig.verify_iff_publicOpChecked, VG.Proof.RsaPkcs1Sig.recoverEnc]
  by_cases hs : sig.length = nB.length
  · rw [ite_eq_left hs]
    simp only [hs, true_and]
    cases hp : publicOpChecked nB eB sig with
    | none => simp
    | some em =>
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨em', he, rfl⟩
        rw [VG.Proof.RsaPkcs1Sig.drop_of_encode he, ite_eq_left he]
      · intro hr
        by_cases he : encode h (em.drop (nB.length - h.len)) nB.length = some em
        · rw [ite_eq_left he, Option.some.injEq] at hr
          exact ⟨em, hr ▸ he, rfl⟩
        · rw [ite_eq_right he] at hr; cases hr
  · rw [ite_eq_right hs]
    simp [hs]

end VG.Proof.RsaPkcs1Sig

end
