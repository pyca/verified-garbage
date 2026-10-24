module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash

/-!
# Deterministic ECDSA over brainpoolP256r1 with HMAC-SHA-256 on 32-bit ARM

The hash function for the generic proof: SHA-256's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.Arm.sha256OKF`), and `vg_ecdsa_brainpoolp256r1_sign`,
with brainpoolP256r1's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcArm` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Sha256

open VG VG.Arm

theorem implies :
    (rfcArm Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst 240).Implies
      (Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signContract Arm.abi 240) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR]
        all_goals simp only [Abi.constRegions, List.map_nil, List.not_mem_nil, false_implies, forall_const]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1, fun c hc => by cases hc⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR] [satState 32 32] using satState 32 32 }

/-- SHA-256, for brainpoolP256r1's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) : RfcHash where
  R := brainpoolp256r1 hL
  I := Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst
  F := Proof.Pbkdf2.Whole.Arm.sha256F
  ok := Proof.Pbkdf2.Whole.Arm.sha256OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha256.hash x).length = 32
    rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  hDB := .inl ⟨rfl, rfl⟩
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signContract Arm.abi 240) :=
  Arm.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Sha256
