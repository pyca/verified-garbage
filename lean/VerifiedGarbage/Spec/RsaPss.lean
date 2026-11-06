module

public import VerifiedGarbage.Spec.Mgf1

/-!
# RSASSA-PSS (RFC 8017 §8.1, EMSA-PSS §9.1)

**Trusted** (as every file in `Spec/`). The signature scheme RSASSA-PSS of
PKCS #1 v2.2 (RFC 8017): its encoding method EMSA-PSS (§9.1), with the hash
function `H` and the mask generation function MGF1 (Appendix B.2.1) with the
hash function `G`, its signature operation (§8.1.1) with the private key,
and its verification operation (§8.1.2) with the public key `(n, e)`. Any
of the library's hash functions (`Mgf1.hashes`) may be either.

As in BoringSSL (`RSA_sign_pss_mgf1`, `RSA_verify_pss_mgf1`), the message is
given as its digest `mHash = Hash(M)` (§9.1.1 step 2, §9.1.2 step 2), which
must be `hLen` octets, and the salt is an input to the encoding: the caller
generates it (§9.1.1 step 4), with a salt length of its choosing.

Verification (`verifyEncoding`) recovers the salt as BoringSSL's
`RSA_verify_PKCS1_PSS_mgf1` (`crypto/fipsmodule/rsa/padding.cc.inc`) does.
Its step 10 takes `DB` to be zeros, an octet `0x01` and the salt, finding the
`0x01` as the first nonzero octet, and then checks the salt's length if one
is expected. For an expected salt length `sLen` this is RFC 8017's
`EMSA-PSS-VERIFY`, as RFC 8017 writes it (`verifyEncodingRfc`: the leftmost
`emLen - hLen - sLen - 2` octets of `DB` zero and the next `0x01`), which
`verifyEncoding_some` proves. Only with no expected length (BoringSSL's
`RSA_PSS_SALTLEN_AUTO`), which RFC 8017 does not have, is it BoringSSL's
alone: it accepts a salt of any length, and step 3 checks only
`emLen ≥ hLen + 2`.

The modulus `n` has `modBits` bits, and EMSA-PSS encodes into `emBits =
modBits - 1` bits, `emLen = ⌈emBits / 8⌉` octets, which is the modulus'
length `k` or, if `modBits - 1` is a multiple of 8, `k - 1`. The integer
`OS2IP(EM)` is below `2^emBits`, hence below `n`, and as `k` octets
(`encodeK`) it is the input of RSASP1; RSAVP1 gives `k` octets, whose first
`k - emLen` must be zero (I2OSP's error in §8.1.2 step 2.c).

Signing (§8.1.1) is the private-key operation on `encodeK`, checked against
the public exponent as BoringSSL checks every private-key operation
(`Rsa.privateChecked`): the signature is released only if RSAVP1 takes it
back to the encoding. Verification takes the public key within BoringSSL's
limits (`Rsa.publicOpChecked`).
-/

@[expose] public section

namespace VG.Spec.RsaPss

open Mgf1 (Hash xorBytes mgf1)
open Rsa (os2ip publicOpChecked privateChecked Outcome)

/-- `n` zero octets. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

/-- The number of bits of `n > 0`: `modBits`. -/
def bitLength (n : Nat) : Nat := Nat.log2 n + 1

/-- `emLen = ⌈emBits / 8⌉`. -/
def emLength (emBits : Nat) : Nat := (emBits + 7) / 8

/-- The octet string `bs` with its leftmost `z ≤ 7` bits set to zero (§9.1.1
step 11, §9.1.2 step 9, with `z = 8 emLen - emBits`). -/
def clearTop (z : Nat) : List Byte → List Byte
  | [] => []
  | b :: bs => (b &&& ((0xFF : Byte) >>> z)) :: bs

/-! ## EMSA-PSS (§9.1) -/

variable (H G : Hash)

/-- `EMSA-PSS-ENCODE` (§9.1.1) of the digest `mHash` with the salt `salt`,
into `emBits` bits, with the hash function `H` and MGF1 with `G`: `EM`, of
`emLen` octets, or `none` (an encoding error) if `mHash` is not `hLen`
octets or `emLen < hLen + sLen + 2`. -/
def encode (mHash salt : List Byte) (emBits : Nat) : Option (List Byte) :=
  let emLen := emLength emBits
  -- Steps 2 and 3.
  if mHash.length ≠ H.len ∨ emLen < H.len + salt.length + 2 then none else
    -- Steps 5 and 6.
    let h := H.hash (zeros 8 ++ mHash ++ salt)
    -- Steps 7 and 8.
    let db := zeros (emLen - salt.length - H.len - 2) ++ 0x01 :: salt
    -- Steps 9–11.
    let maskedDB := clearTop (8 * emLen - emBits) (xorBytes db (mgf1 G h (emLen - H.len - 1)))
    -- Step 12.
    some (maskedDB ++ h ++ [0xbc])

/-- `EMSA-PSS-VERIFY` (§9.1.2) of the encoding `em` of `emBits` bits for the
digest `mHash`, with the hash function `H` and MGF1 with `G`, expecting the
salt length `sLen` (or any, if `none`), with BoringSSL's step 10: whether it
is consistent. -/
def verifyEncoding (mHash em : List Byte) (emBits : Nat) (sLen : Option Nat) : Bool :=
  let emLen := emLength emBits
  let z := 8 * emLen - emBits
  -- Steps 2 and 3, and that `em` is `emLen` octets.
  if mHash.length ≠ H.len ∨ em.length ≠ emLen ∨ emLen < H.len + sLen.getD 0 + 2 then false
  -- Step 4.
  else if em.getLast? ≠ some 0xbc then false
  else
    -- Step 5.
    let maskedDB := em.take (emLen - H.len - 1)
    let h := (em.drop (emLen - H.len - 1)).take H.len
    -- Step 6.
    if clearTop z maskedDB ≠ maskedDB then false
    else
      -- Steps 7–9.
      let db := clearTop z (xorBytes maskedDB (mgf1 G h (emLen - H.len - 1)))
      -- Steps 10 and 11, as BoringSSL: zeros, `0x01`, then the salt.
      match db.dropWhile (· == 0) with
      | 0x01 :: salt =>
        -- Steps 12–14.
        sLen.all (· == salt.length) && H.hash (zeros 8 ++ mHash ++ salt) == h
      | _ => false

/-- `EMSA-PSS-VERIFY` (§9.1.2) of the encoding `em` of `emBits` bits for the
digest `mHash`, with the hash function `H` and MGF1 with `G`, for the salt
length `sLen`, as RFC 8017 writes it: whether it is consistent. Only
`verifyEncoding_some` uses it: `verifyEncoding` with an expected salt length
is this. -/
def verifyEncodingRfc (mHash em : List Byte) (emBits sLen : Nat) : Bool :=
  let emLen := emLength emBits
  let z := 8 * emLen - emBits
  -- Steps 2 and 3, and that `em` is `emLen` octets.
  if mHash.length ≠ H.len ∨ em.length ≠ emLen ∨ emLen < H.len + sLen + 2 then false
  -- Step 4.
  else if em.getLast? ≠ some 0xbc then false
  else
    -- Step 5.
    let maskedDB := em.take (emLen - H.len - 1)
    let h := (em.drop (emLen - H.len - 1)).take H.len
    -- Step 6.
    if clearTop z maskedDB ≠ maskedDB then false
    else
      -- Steps 7–9.
      let db := clearTop z (xorBytes maskedDB (mgf1 G h (emLen - H.len - 1)))
      -- Step 10: the leftmost `emLen - hLen - sLen - 2` octets of `DB` are zero, and the
      -- octet at position `emLen - hLen - sLen - 1` (the leftmost is position 1) is `0x01`.
      if db.take (emLen - H.len - sLen - 2) ≠ zeros (emLen - H.len - sLen - 2) ∨
          db[emLen - H.len - sLen - 2]? ≠ some 0x01 then false
      else
        -- Step 11: the salt is the last `sLen` octets of `DB`.
        let salt := db.drop (db.length - sLen)
        -- Steps 12–14.
        H.hash (zeros 8 ++ mHash ++ salt) == h

/-- Zeros, `0x01` and `salt`, past its leading zeros, is `0x01` and `salt`. -/
theorem dropWhile_db (p : Nat) (salt : List Byte) :
    (zeros p ++ 0x01 :: salt).dropWhile (· == 0) = 0x01 :: salt := by
  induction p with
  | zero => simp [zeros]
  | succ p ih => simp [zeros, List.replicate_succ] at ih ⊢

/-- An octet string whose first nonzero octet is `0x01`, followed by `salt`,
is zeros, `0x01` and `salt`. -/
theorem eq_db {db salt : List Byte} (h : db.dropWhile (· == 0) = 0x01 :: salt) :
    db = zeros (db.length - salt.length - 1) ++ 0x01 :: salt := by
  have hz : db.takeWhile (· == 0) = zeros (db.takeWhile (· == 0)).length := by
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl, fun b hb => ?_⟩
    simpa using List.all_eq_true.mp List.all_takeWhile b hb
  have hd := List.takeWhile_append_dropWhile (p := (· == (0 : Byte))) (l := db)
  rw [h, hz] at hd
  have hl := congrArg List.length hd
  simp only [zeros, List.length_append, List.length_replicate, List.length_cons] at hl
  rw [← hd]
  simp only [zeros, List.length_append, List.length_replicate, List.length_cons]
  congr 2
  omega

/-- An octet string whose leftmost `p` octets are zero and whose next is
`0x01` is zeros, `0x01` and the rest. -/
theorem eq_db_of_take {db : List Byte} {p : Nat} (h₁ : db.take p = zeros p)
    (h₂ : db[p]? = some 0x01) : db = zeros p ++ 0x01 :: db.drop (p + 1) := by
  obtain ⟨hp, he⟩ := List.getElem?_eq_some_iff.mp h₂
  have h := List.take_append_drop p db
  rw [List.drop_eq_getElem_cons hp, he, h₁] at h
  exact h.symm

/-- With an expected salt length, `verifyEncoding` (BoringSSL's step 10) is
`EMSA-PSS-VERIFY` as RFC 8017 writes it, for MGF1 with a hash function `G`
whose digests are `hLen > 0` octets. -/
theorem verifyEncoding_some (hG : 0 < G.len) (hGl : ∀ x, (G.hash x).length = G.len)
    (mHash em : List Byte) (emBits sLen : Nat) :
    verifyEncoding H G mHash em emBits (some sLen) = verifyEncodingRfc H G mHash em emBits sLen := by
  unfold verifyEncoding verifyEncodingRfc
  simp only [Option.getD_some, Option.all_some]
  split
  · rfl
  rename_i c₁
  simp only [not_or, Decidable.not_not, Nat.not_lt] at c₁
  obtain ⟨-, hl, hlen⟩ := c₁
  split
  · rfl
  split
  · rfl
  generalize hL : emLength emBits - H.len - 1 = L
  generalize hh : (em.drop L).take H.len = h
  have hmask : (mgf1 G h L).length = L := by
    have hfl : ((List.range ((L + G.len - 1) / G.len)).flatMap fun c =>
        G.hash (h ++ Rsa.i2osp c 4)).length = G.len * ((L + G.len - 1) / G.len) := by
      rw [List.length_flatMap]
      simp only [hGl, List.map_const', List.length_range, List.sum_replicate_nat, Nat.mul_comm]
    have hd := Nat.div_add_mod (L + G.len - 1) G.len
    have hm := Nat.mod_lt (L + G.len - 1) hG
    simp only [mgf1, List.length_take, hfl]
    omega
  generalize hdb : clearTop (8 * emLength emBits - emBits) (xorBytes (em.take L) (mgf1 G h L)) = db
  have hdl : db.length = L := by
    have : ∀ z (bs : List Byte), (clearTop z bs).length = bs.length := by
      intro z bs; cases bs <;> rfl
    rw [← hdb, this, xorBytes, List.length_zipWith, List.length_take, hmask]
    omega
  generalize hp : emLength emBits - H.len - sLen - 2 = p
  have hpl : db.length = p + 1 + sLen := by omega
  have hrest : ∀ rest, db = zeros p ++ 0x01 :: rest → rest.length = sLen := by
    rintro rest rfl
    simp [zeros] at hpl
    omega
  split
  · rename_i salt hd
    by_cases hs : salt.length = sLen
    · have he : db = zeros p ++ 0x01 :: salt := by
        rw [eq_db hd]
        congr 2
        omega
      have hdrop : db.drop (db.length - sLen) = salt := by
        rw [show db.length - sLen = p + 1 by omega, he,
          show zeros p ++ 0x01 :: salt = (zeros p ++ [0x01]) ++ salt by simp,
          List.drop_left' (by simp [zeros])]
      rw [hdrop]
      subst he
      simp [zeros, hs]
    · have hc : db.take p ≠ zeros p ∨ db[p]? ≠ some 0x01 := by
        refine Decidable.or_iff_not_imp_left.mpr fun h₁ h₂ => hs ?_
        have he := eq_db_of_take (Decidable.not_not.mp h₁) h₂
        have hw := dropWhile_db p (db.drop (p + 1))
        rw [← he, hd, List.cons.injEq] at hw
        rw [hw.2]
        exact hrest _ he
      simp only [hc, ↓reduceIte]
      simp [Ne.symm hs]
  · rename_i hd
    have hc : db.take p ≠ zeros p ∨ db[p]? ≠ some 0x01 := by
      refine Decidable.or_iff_not_imp_left.mpr fun h₁ h₂ => ?_
      have he := eq_db_of_take (Decidable.not_not.mp h₁) h₂
      have hw := dropWhile_db p (db.drop (p + 1))
      rw [← he] at hw
      exact hd _ hw
    simp only [hc, ↓reduceIte]

/-! ## RSASSA-PSS (§8.1) -/

/-- The encoding of the digest `mHash` with the salt `salt` for the modulus
`nB` (`k` octets), as `k` octets: §8.1.1 step 1's `EM = EMSA-PSS-ENCODE(M,
modBits - 1)`, then `m = OS2IP(EM)` as `k` octets, the input of RSASP1
(step 2.a–b); or `none` if the encoding fails. -/
def encodeK (nB mHash salt : List Byte) : Option (List Byte) :=
  let emBits := bitLength (os2ip nB) - 1
  (encode H G mHash salt emBits).map (zeros (nB.length - emLength emBits) ++ ·)

/-- `RSASSA-PSS-VERIFY((n, e), M, S)` (§8.1.2) of the signature `sB` for the
digest `mHash`, with the public key `(nB, eB)`, the hash function `H` and
MGF1 with `G`, expecting the salt length `sLen` (or any, if `none`): whether
the signature is valid. Step 1: `sB` is `k` octets; step 2: RSAVP1, and
`EM = I2OSP(m, emLen)`, which requires the first `k - emLen` octets of `m`
to be zero; step 3: `EMSA-PSS-VERIFY`. RSAVP1 is `publicOpChecked`, within
BoringSSL's limits on the public key (`rsa_check_public_key`). -/
def verify (nB eB mHash sB : List Byte) (sLen : Option Nat) : Bool :=
  let k := nB.length
  let emBits := bitLength (os2ip nB) - 1
  let emLen := emLength emBits
  sB.length == k &&
    match publicOpChecked nB eB sB with
    | some x => x.take (k - emLen) == zeros (k - emLen) &&
        verifyEncoding H G mHash (x.drop (k - emLen)) emBits sLen
    | none => false

/-- `RSASSA-PSS-SIGN(K, M)` (§8.1.1) of the digest `mHash` with the salt
`salt`, with the private key `(p, q, dP, dQ, qInv)` of the modulus `nB` and
the public exponent `eB`, the hash function `H` and MGF1 with `G`: step 1,
`encodeK`, then step 2, RSASP1 checked against `e` (`privateChecked`). The
outcome is `ok` with the signature (`k` octets), `invalid` if the encoding
fails or `privateChecked` refuses the key, or `fault` (the internal error)
if the result fails the check against `e`. -/
def sign (nB eB pB qB dPB dQB qInvB mHash salt : List Byte) : Outcome :=
  match encodeK H G nB mHash salt with
  | some em => privateChecked nB eB em pB qB dPB dQB qInvB
  | none => .invalid

end VG.Spec.RsaPss
