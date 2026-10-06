import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-256 on 32-bit ARM

The hash function for the generic proof: SHA-256's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.Arm.sha256OKF`), and `vg_ecdsa_p256_sign`,
with P-256's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcArm` (`implies`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm.Sha256

open VG VG.Arm

theorem implies :
    (rfcArm Spec.Ecdsa.Rfc6979.P256Sha256.inst 240).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract Arm.abi 240) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR] [satState 32 32] using satState 32 32 }

/-- SHA-256, for P-256's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P256.curve) : RfcHash where
  R := p256 hL
  I := Spec.Ecdsa.Rfc6979.P256Sha256.inst
  F := Proof.Pbkdf2.Whole.Arm.sha256F
  ok := Proof.Pbkdf2.Whole.Arm.sha256OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha256.hash x).length = 32
    rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _
  tries := rfl
  hDB := .inl ⟨rfl, rfl⟩
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract Arm.abi 240) :=
  Arm.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.Sha256
