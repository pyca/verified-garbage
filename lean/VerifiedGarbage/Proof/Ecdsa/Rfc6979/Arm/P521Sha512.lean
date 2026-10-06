import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512

/-!
# Deterministic ECDSA over P-521 with HMAC-SHA-512 on 32-bit ARM

The hash function for the generic proof: SHA-512's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.Arm.sha512OKF`), and `vg_ecdsa_p521_sign`,
with P-521's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcArm` (`implies`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm.P521Sha512

open VG VG.Arm

theorem implies :
    (rfcArm Spec.Ecdsa.Rfc6979.P521Sha512.inst 384).Implies
      (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract Arm.abi 384) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm, stkR] [satState 66 64] using satState 66 64 }

/-- SHA-512, for P-521's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P521.curve) : RfcHash where
  R := p521 hL
  I := Spec.Ecdsa.Rfc6979.P521Sha512.inst
  F := Proof.Pbkdf2.Whole.Arm.sha512F
  ok := Proof.Pbkdf2.Whole.Arm.sha512OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha512.finalHash Spec.Sha512.H0_512 x).length = 64
    exact Proof.Hmac.Generic.Common.finalHash_length _ _
  tries := rfl
  hDB := .inr (.inr ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := ⟨rfl, rfl⟩

theorem sign_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract Arm.abi 384) :=
  Arm.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.P521Sha512
