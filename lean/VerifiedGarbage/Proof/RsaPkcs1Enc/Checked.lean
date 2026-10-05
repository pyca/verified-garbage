import VerifiedGarbage.Spec.RsaPkcs1Enc
import VerifiedGarbage.Proof.Rsa.Checked
import Mathlib.Data.Fintype.Card

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt`. -/
section

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
    | ok EM => simp [VG.Proof.RsaPkcs1Enc.decryptWith_of_ok h.1 h.2 hEM, h]
    | invalid => simp [VG.Proof.RsaPkcs1Enc.decryptWith_of_invalid (k := k) (dB := dB) hEM]
    | fault => simp [VG.Proof.RsaPkcs1Enc.decryptWith_of_fault (dB := dB) h.1 h.2 hEM]
  · simp only [VG.Proof.RsaPkcs1Enc.decryptWith_of_length h, reduceCtorEq, exists_false, false_iff]
    omega

theorem decryptWith_of_valid {rsadp : List Byte → Outcome} {k : Nat}
    {dB C EM : List Byte} (hC : C.length = k) (hk : 11 ≤ k) (hEM : rsadp C = .ok EM)
    (hv : valid EM = true) :
    decryptWith rsadp k dB C = .ok (lastN (msgLength EM) EM) := by
  rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_ok hC hk hEM, implicitDecode, hv]
  rfl

/-- For an invalid padding, the message is a function of `k`, `d` and the
ciphertext alone. -/
theorem decryptWith_of_not_valid {rsadp : List Byte → Outcome} {k : Nat}
    {dB C EM : List Byte} (hC : C.length = k) (hk : 11 ≤ k) (hEM : rsadp C = .ok EM)
    (hlen : EM.length = k) (hv : valid EM = false) :
    decryptWith rsadp k dB C = .ok (alternative k dB C) := by
  rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_ok hC hk hEM, implicitDecode, hv, hlen]
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
  Nat.le_trans (VG.Proof.RsaPkcs1Enc.lastN_length_le _ _) (VG.Proof.RsaPkcs1Enc.altLength_le _ _)

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
  rw [separator, h, VG.Proof.RsaPkcs1Enc.findIdx?_append_zero PS M hPS]
  rfl

theorem encode_length (M PS : List Byte) : (encode M PS).length = PS.length + M.length + 3 := by
  simp [encode]
  omega

theorem valid_encode (M PS : List Byte) (hPS : PS.all (· != 0) = true) (h8 : 8 ≤ PS.length) :
    valid (encode M PS) = true := by
  simp only [valid, VG.Proof.RsaPkcs1Enc.separator_encode M PS hPS]
  simp [encode]
  omega

theorem msgLength_encode (M PS : List Byte) (hPS : PS.all (· != 0) = true) :
    msgLength (encode M PS) = M.length := by
  simp only [msgLength, VG.Proof.RsaPkcs1Enc.separator_encode M PS hPS, VG.Proof.RsaPkcs1Enc.encode_length]
  omega

theorem lastN_encode (M PS : List Byte) : lastN M.length (encode M PS) = M := by
  have h : encode M PS = ([0x00, 0x02] ++ PS ++ [0x00]) ++ M := by simp [encode]
  rw [lastN, h, List.length_append]
  simp

/-- A valid encoding decodes to its message. -/
theorem implicitDecode_encode (dB C M PS : List Byte) (hPS : PS.all (· != 0) = true)
    (h8 : 8 ≤ PS.length) : implicitDecode dB C (encode M PS) = M := by
  simp only [implicitDecode, VG.Proof.RsaPkcs1Enc.valid_encode M PS hPS h8, ite_true, VG.Proof.RsaPkcs1Enc.msgLength_encode M PS hPS,
    VG.Proof.RsaPkcs1Enc.lastN_encode]

/-! ## Round trip -/

theorem i2osp_length (x n : Nat) : (Spec.Rsa.i2osp x n).length = n := by simp [Spec.Rsa.i2osp]

theorem publicOp_length {nB eB xB C : List Byte} (h : Spec.Rsa.publicOp nB eB xB = some C) :
    C.length = nB.length := by
  dsimp only [Spec.Rsa.publicOp] at h
  split at h
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact VG.Proof.RsaPkcs1Enc.i2osp_length _ _
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
    have hEM : (encode M PS).length = nB.length := by rw [VG.Proof.RsaPkcs1Enc.encode_length]; omega
    have hC : C.length = nB.length := by
      dsimp only [Spec.Rsa.publicOpChecked] at h
      split at h
      · exact VG.Proof.RsaPkcs1Enc.publicOp_length h
      · cases h
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by omega) (hinv _ _ hEM h),
      VG.Proof.RsaPkcs1Enc.implicitDecode_encode dB C M PS hPS (by omega)]
  · cases h

end VG.Proof.RsaPkcs1Enc

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Enc.Checked`. -/
section

/-!
# RSAES-PKCS1-v1_5 decryption with RSADP checked against `e`

`decrypt` is `decryptWith` with `Rsa.privateChecked`. For any key:

* `decrypt_of_length`, `decrypt_of_ge`: a ciphertext that is not `k` octets
  long, or not below `n`, gives `invalid`.
* `decrypt_of_valid`, `decrypt_of_not_valid`: if RSADP gives `EM`, the
  message of `EM` for a valid padding, and otherwise `alternative k dB C`,
  a function of `d` and the ciphertext alone; `decrypt_ne_fault`: `fault`
  only if RSADP's check against `e` fails.

For a key `Rsa.checkKey` (BoringSSL's `RSA_check_key`) accepts whose `p`
and `q` are prime:

* `decrypt_of_checkKey`: every `k`-octet ciphertext below `n` decrypts, to
  `implicitDecode` of `c^d mod n`; so (`decrypt_eq_invalid_iff`,
  `decrypt_checkKey_ne_fault`) decryption gives an error only for a
  ciphertext that is not `k` octets long or not below `n`, never `fault`,
  and never for the padding.
* `decrypt_encrypt`: decrypting what `encrypt` gives with the public key
  `(n, e)` returns the message.
-/

namespace VG.Proof.RsaPkcs1Enc

open Spec.RsaPkcs1Enc
open Spec.Rsa (Outcome os2ip i2osp privateChecked checkKey modulusValid publicOpChecked)
open Proof.Rsa (lt_of_os2ip os2ip_i2osp i2osp_length)

variable {nB eB dB pB qB dPB dQB qInvB C : List Byte}

/-- OS2IP then I2OSP to the same length is the identity. -/
theorem i2osp_os2ip (bs : List Byte) : i2osp (os2ip bs) bs.length = bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    rw [List.length_append, List.length_singleton, Proof.Rsa.i2osp_succ, Proof.Rsa.os2ip_snoc]
    have hb := b.isLt
    rw [show (256 * os2ip bs + b.toNat) / 256 = os2ip bs by omega, ih]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

/-- A valid modulus is at least 64 octets long. -/
theorem le_of_modulusValid (h : modulusValid (os2ip nB) nB.length = true) : 64 ≤ nB.length := by
  simp only [modulusValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hlt := lt_of_os2ip nB
  refine Nat.le_of_not_lt fun hk => ?_
  have h1 : 2 ^ 511 < 2 ^ (8 * nB.length) := by
    rw [Nat.pow_mul, show (2 : Nat) ^ 8 = 256 from rfl]
    omega
  have h2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h1
  omega

/-- `privateChecked` refuses every input that is not below `n`. -/
theorem privateChecked_of_ge (xB : List Byte) (hx : os2ip nB ≤ os2ip xB) :
    privateChecked nB eB xB pB qB dPB dQB qInvB = .invalid := by
  have : ¬ os2ip xB < os2ip nB := by omega
  simp [privateChecked, Spec.Rsa.decryptChecked, Spec.Rsa.decryptCrt, this]

theorem decrypt_of_length (h : C.length ≠ nB.length) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .invalid :=
  VG.Proof.RsaPkcs1Enc.decryptWith_of_length (by omega)

theorem decrypt_of_ge (h : os2ip nB ≤ os2ip C) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .invalid :=
  VG.Proof.RsaPkcs1Enc.decryptWith_of_invalid (VG.Proof.RsaPkcs1Enc.privateChecked_of_ge C h)

/-- `privateChecked` gives `ok` only for a valid modulus. -/
theorem modulusValid_of_ok {xB y : List Byte}
    (h : privateChecked nB eB xB pB qB dPB dQB qInvB = .ok y) :
    modulusValid (os2ip nB) nB.length = true := by
  simp only [privateChecked] at h
  split at h
  · rename_i hv; exact hv.1
  · cases h

theorem decrypt_of_ok {EM : List Byte} (hC : C.length = nB.length)
    (hEM : privateChecked nB eB C pB qB dPB dQB qInvB = .ok EM) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .ok (implicitDecode dB C EM) :=
  VG.Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by have := VG.Proof.RsaPkcs1Enc.le_of_modulusValid (VG.Proof.RsaPkcs1Enc.modulusValid_of_ok hEM); omega) hEM

/-- For a valid padding, decryption returns the message of `EM`. -/
theorem decrypt_of_valid {EM : List Byte} (hC : C.length = nB.length)
    (hEM : privateChecked nB eB C pB qB dPB dQB qInvB = .ok EM) (hv : valid EM = true) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .ok (lastN (msgLength EM) EM) := by
  rw [VG.Proof.RsaPkcs1Enc.decrypt_of_ok hC hEM, implicitDecode, hv]
  rfl

/-- For an invalid padding, decryption returns `alternative k dB C`, a
function of the length of the modulus, `d` and the ciphertext alone. -/
theorem decrypt_of_not_valid {EM : List Byte} (hC : C.length = nB.length)
    (hEM : privateChecked nB eB C pB qB dPB dQB qInvB = .ok EM) (hv : valid EM = false) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .ok (alternative nB.length dB C) := by
  rw [VG.Proof.RsaPkcs1Enc.decrypt_of_ok hC hEM, implicitDecode, hv, (Proof.Rsa.privateChecked_ok hEM).1]
  rfl

/-- Decryption gives the internal error only if RSADP's check against `e`
fails. -/
theorem decrypt_ne_fault (h : privateChecked nB eB C pB qB dPB dQB qInvB ≠ .fault) :
    decrypt nB eB dB pB qB dPB dQB qInvB C ≠ .fault := by
  dsimp only [decrypt, decryptWith]
  split
  · cases hc : privateChecked nB eB C pB qB dPB dQB qInvB with
    | ok EM => nofun
    | invalid => nofun
    | fault => exact absurd hc h
  · nofun

/-! ## Keys `checkKey` accepts -/

variable (hk : checkKey nB eB dB pB qB dPB dQB qInvB = true) (hp : (os2ip pB).Prime)
  (hq : (os2ip qB).Prime)

include hk in
theorem modulusValid_of_checkKey : modulusValid (os2ip nB) nB.length = true := by
  simp only [checkKey, Spec.Rsa.keyValid, Bool.and_eq_true] at hk
  exact hk.1.1.1.1.1.1.1.1.1.1.1.1.1

include hk hp hq in
/-- Every `k`-octet ciphertext below `n` decrypts, to `implicitDecode` of
`c^d mod n`. -/
theorem decrypt_of_checkKey (hC : C.length = nB.length) (hc : os2ip C < os2ip nB) :
    decrypt nB eB dB pB qB dPB dQB qInvB C =
      .ok (implicitDecode dB C (i2osp (os2ip C ^ os2ip dB % os2ip nB) nB.length)) :=
  VG.Proof.RsaPkcs1Enc.decrypt_of_ok hC (Proof.Rsa.privateChecked_of_checkKey hk hp hq hc)

include hk hp hq in
/-- Decryption gives an error only for a ciphertext that is not `k` octets
long or not below `n`. -/
theorem decrypt_eq_invalid_iff :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .invalid ↔
      C.length ≠ nB.length ∨ os2ip nB ≤ os2ip C := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    have hC : C.length = nB.length := by omega
    have hc : os2ip C < os2ip nB := by omega
    rw [VG.Proof.RsaPkcs1Enc.decrypt_of_checkKey hk hp hq hC hc] at h
    cases h
  · rintro (h | h)
    · exact VG.Proof.RsaPkcs1Enc.decrypt_of_length h
    · exact VG.Proof.RsaPkcs1Enc.decrypt_of_ge h

include hk hp hq in
/-- Decryption never gives the internal error. -/
theorem decrypt_checkKey_ne_fault : decrypt nB eB dB pB qB dPB dQB qInvB C ≠ .fault :=
  VG.Proof.RsaPkcs1Enc.decrypt_ne_fault (Proof.Rsa.privateChecked_ne_fault C hk hp hq)

/-! ## Round trip -/

include hk hp hq in
/-- `x ↦ x^e mod n` is injective below `n`: `c ↦ c^d mod n` is its right
inverse there (the check of `privateChecked` passes for every `c < n`), and
a function from a finite set to itself with a right inverse is a bijection. -/
theorem pow_e_injective {x y : Nat} (hx : x < os2ip nB) (hy : y < os2ip nB)
    (h : x ^ os2ip eB % os2ip nB = y ^ os2ip eB % os2ip nB) : x = y := by
  have hn : 0 < os2ip nB := by omega
  -- `c^d mod n` then `· ^ e mod n` is the identity below `n`.
  have hinv : ∀ c < os2ip nB, (c ^ os2ip dB % os2ip nB) ^ os2ip eB % os2ip nB = c := by
    intro c hc
    have hok := Proof.Rsa.privateChecked_of_checkKey hk hp hq
      (show os2ip (i2osp c nB.length) < os2ip nB by
        rw [os2ip_i2osp, Nat.mod_eq_of_lt (Nat.lt_trans hc (lt_of_os2ip nB))]; exact hc)
    have := (Proof.Rsa.privateChecked_ok hok).2.2
    rwa [os2ip_i2osp, os2ip_i2osp, Nat.mod_eq_of_lt (Nat.lt_trans hc (lt_of_os2ip nB)),
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn) (lt_of_os2ip nB))] at this
  let N := os2ip nB
  let F : Fin N → Fin N := fun c => ⟨c.1 ^ os2ip dB % N, Nat.mod_lt _ hn⟩
  let G : Fin N → Fin N := fun c => ⟨c.1 ^ os2ip eB % N, Nat.mod_lt _ hn⟩
  have hGF : Function.LeftInverse G F := fun c => Fin.ext (hinv c.1 c.2)
  have hFs : Function.Surjective F := Finite.injective_iff_surjective.mp hGF.injective
  -- So `F ∘ G` is the identity too, and `G` is injective.
  have hFG : Function.RightInverse G F := fun c => by
    obtain ⟨a, rfl⟩ := hFs c
    rw [hGF a]
  have := congrArg Fin.val (hFG.injective (show G ⟨x, hx⟩ = G ⟨y, hy⟩ from Fin.ext h))
  exact this

include hk hp hq in
/-- Decrypting what `encrypt` gives with the public key `(n, e)` returns the
message. -/
theorem decrypt_encrypt {M PS : List Byte} (h : encrypt nB eB M PS = some C) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .ok M := by
  refine VG.Proof.RsaPkcs1Enc.decryptWith_encrypt (fun x c hx hxc => ?_) dB h
  have hv := VG.Proof.RsaPkcs1Enc.modulusValid_of_checkKey hk
  have hn : 0 < os2ip nB := by
    simp only [modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hv; omega
  -- `c = x^e mod n` for `x < n`.
  simp only [publicOpChecked, Spec.Rsa.publicOp, hv, ite_true, Spec.Rsa.encrypt] at hxc
  split at hxc
  · split at hxc
    · rename_i hxn
      simp only [Option.map_some, Option.some.injEq] at hxc
      subst hxc
      rw [Proof.Bignum.powMod_eq] at *
      have hc : os2ip (i2osp (os2ip x ^ os2ip eB % os2ip nB) nB.length) < os2ip nB := by
        rw [os2ip_i2osp, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn) (lt_of_os2ip nB))]
        exact Nat.mod_lt _ hn
      have hok := Proof.Rsa.privateChecked_of_checkKey hk hp hq hc
      obtain ⟨-, hlt, hpow⟩ := Proof.Rsa.privateChecked_ok hok
      rw [hok]
      -- The result `y` has `y^e mod n = x^e mod n`, so it is `x`.
      have hy := VG.Proof.RsaPkcs1Enc.pow_e_injective hk hp hq hlt hxn (by
        rw [hpow, os2ip_i2osp, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn) (lt_of_os2ip nB))])
      rw [os2ip_i2osp, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn) (lt_of_os2ip nB))] at hy
      rw [hy, ← hx, VG.Proof.RsaPkcs1Enc.i2osp_os2ip]
    · cases hxc
  · cases hxc

end VG.Proof.RsaPkcs1Enc

end
