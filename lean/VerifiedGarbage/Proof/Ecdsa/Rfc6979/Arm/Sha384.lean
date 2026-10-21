module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-384 on 32-bit ARM

The hash function for the generic proof: SHA-384's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.Arm.sha384OKF`), and `vg_ecdsa_p256_sign`,
with P-256's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcArm` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm.Sha384

open VG VG.Arm

theorem implies :
    (rfcArm Spec.Ecdsa.Rfc6979.P256Sha384.inst 240).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract Arm.abi 240) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR]
        all_goals simp only [Abi.constRegions, List.map_nil, List.not_mem_nil, false_implies, forall_const]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1, fun c hc => by cases hc⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR] [satState 32 48] using satState 32 48 }

/-- SHA-384, for P-256's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P256.curve) : RfcHash where
  R := p256 hL
  I := Spec.Ecdsa.Rfc6979.P256Sha384.inst
  F := Proof.Pbkdf2.Whole.Arm.sha384F
  ok := Proof.Pbkdf2.Whole.Arm.sha384OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show ((Spec.Sha512.finalHash Spec.Sha512.H0_384 x).take 48).length = 48
    rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; rfl
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract Arm.abi 240) :=
  Arm.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.Sha384
