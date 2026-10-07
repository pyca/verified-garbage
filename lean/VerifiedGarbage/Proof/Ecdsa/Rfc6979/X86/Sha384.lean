import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CombContract
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P256
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-384 on x86 (32-bit)

The hash function for the generic proof: SHA-384's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.X86.sha384OKF`), and `vg_ecdsa_p256_sign`,
with P-256's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcWide` (`implies`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86.Sha384

open VG VG.X86

theorem implies :
    (rfcWide Spec.Ecdsa.Rfc6979.P256Sha384.inst 272 Impl.Ecdsa.X86.p256Comb.combConsts).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract
        (X86.abi.withConsts Impl.Ecdsa.X86.p256Comb.combConsts) 272) :=
  comb_implies _ rfl (by decide)

/-- SHA-384, for P-256's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P256.curve) : RfcHash where
  R := p256 hL
  I := Spec.Ecdsa.Rfc6979.P256Sha384.inst
  F := Proof.Pbkdf2.Whole.X86.sha384F
  ok := Proof.Pbkdf2.Whole.X86.sha384OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show ((Spec.Sha512.finalHash Spec.Sha512.H0_384 x).take 48).length = 48
    rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl
  tries := rfl
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified X86.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (X86.abi.withConsts Impl.Ecdsa.X86.p256Comb.combConsts) 272) :=
  X86.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.X86.Sha384
