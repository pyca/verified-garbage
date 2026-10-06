import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombContract
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P256
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-256 on x86 (32-bit)

The hash function for the generic proof, for any implementation `v` of
SHA-256's compression function: the functions that PBKDF2's code calls
(`Proof.Pbkdf2.Whole.X86.sha256OKF`), and `vg_ecdsa_p256_sign`,
with P-256's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcWide` (`implies`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86.Sha256

open VG VG.X86

theorem implies :
    (rfcWide Spec.Ecdsa.Rfc6979.P256Sha256.inst 272 Impl.Ecdsa.X86.p256Comb.combConsts).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract
        (X86.abi.withConsts Impl.Ecdsa.X86.p256Comb.combConsts) 272) :=
  comb_implies _ rfl (by decide)

open VG.Proof.Sha256.X86.Variants (Backend)

/-- SHA-256 with the backend `v`, for P-256's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P256.curve) (v : Backend) : RfcHash where
  R := p256 hL
  I := Spec.Ecdsa.Rfc6979.P256Sha256.inst
  F := v.F
  ok := Proof.Pbkdf2.Whole.X86.sha256OKF v
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha256.hash x).length = 32
    rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _
  tries := rfl
  hDB := .inl ⟨rfl, rfl⟩
  hS := show 96 ≤ 192 by decide
  hWi := show 104 * 8 ≤ 1872 by decide
  hWf := show 104 * 8 ≤ 1872 by decide
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve) (v : Backend) :
    Verified X86.target (cfgOf (pack hL v)).sign (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract (X86.abi.withConsts Impl.Ecdsa.X86.p256Comb.combConsts) 272) :=
  X86.sign_verified (pack hL v) implies

end VG.Proof.Ecdsa.Rfc6979.X86.Sha256
