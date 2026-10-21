module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash

/-!
# Deterministic ECDSA over P-224 with HMAC-SHA-224 on 32-bit ARM

The hash function for the generic proof: SHA-224's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.Arm.sha224OKF`), and `vg_ecdsa_p224_sign`,
with P-224's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcArm` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm.P224Sha224

open VG VG.Arm

theorem implies :
    (rfcArm Spec.Ecdsa.Rfc6979.P224Sha224.inst 240).Implies
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract Arm.abi 240) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR]
        all_goals simp only [Abi.constRegions, List.map_nil, List.not_mem_nil, false_implies, forall_const]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1, fun c hc => by cases hc⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR] [satState 28 28] using satState 28 28 }

/-- SHA-224, for P-224's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P224.curve) : RfcHash where
  R := p224 hL
  I := Spec.Ecdsa.Rfc6979.P224Sha224.inst
  F := Proof.Pbkdf2.Whole.Arm.sha224F
  ok := Proof.Pbkdf2.Whole.Arm.sha224OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha256.sha224 x).length = 28
    simp [Spec.Sha256.sha224, Spec.Sha256.finalHash, Spec.Sha256.wordBytes,
      List.length_flatMap, List.map_const']
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  hDB := .inr (.inr (.inr ⟨rfl, rfl⟩))
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract Arm.abi 240) :=
  Arm.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.P224Sha224
