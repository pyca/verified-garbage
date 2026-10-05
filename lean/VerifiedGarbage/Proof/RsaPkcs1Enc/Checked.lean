import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Rsa.Checked
import Mathlib.Data.Fintype.Card

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
  decryptWith_of_length (by omega)

theorem decrypt_of_ge (h : os2ip nB ≤ os2ip C) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .invalid :=
  decryptWith_of_invalid (privateChecked_of_ge C h)

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
  decryptWith_of_ok hC (by have := le_of_modulusValid (modulusValid_of_ok hEM); omega) hEM

/-- For a valid padding, decryption returns the message of `EM`. -/
theorem decrypt_of_valid {EM : List Byte} (hC : C.length = nB.length)
    (hEM : privateChecked nB eB C pB qB dPB dQB qInvB = .ok EM) (hv : valid EM = true) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .ok (lastN (msgLength EM) EM) := by
  rw [decrypt_of_ok hC hEM, implicitDecode, hv]
  rfl

/-- For an invalid padding, decryption returns `alternative k dB C`, a
function of the length of the modulus, `d` and the ciphertext alone. -/
theorem decrypt_of_not_valid {EM : List Byte} (hC : C.length = nB.length)
    (hEM : privateChecked nB eB C pB qB dPB dQB qInvB = .ok EM) (hv : valid EM = false) :
    decrypt nB eB dB pB qB dPB dQB qInvB C = .ok (alternative nB.length dB C) := by
  rw [decrypt_of_ok hC hEM, implicitDecode, hv, (Proof.Rsa.privateChecked_ok hEM).1]
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
  decrypt_of_ok hC (Proof.Rsa.privateChecked_of_checkKey hk hp hq hc)

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
    rw [decrypt_of_checkKey hk hp hq hC hc] at h
    cases h
  · rintro (h | h)
    · exact decrypt_of_length h
    · exact decrypt_of_ge h

include hk hp hq in
/-- Decryption never gives the internal error. -/
theorem decrypt_checkKey_ne_fault : decrypt nB eB dB pB qB dPB dQB qInvB C ≠ .fault :=
  decrypt_ne_fault (Proof.Rsa.privateChecked_ne_fault C hk hp hq)

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
  refine decryptWith_encrypt (fun x c hx hxc => ?_) dB h
  have hv := modulusValid_of_checkKey hk
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
      have hy := pow_e_injective hk hp hq hlt hxn (by
        rw [hpow, os2ip_i2osp, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn) (lt_of_os2ip nB))])
      rw [os2ip_i2osp, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hn) (lt_of_os2ip nB))] at hy
      rw [hy, ← hx, i2osp_os2ip]
    · cases hxc
  · cases hxc

end VG.Proof.RsaPkcs1Enc
