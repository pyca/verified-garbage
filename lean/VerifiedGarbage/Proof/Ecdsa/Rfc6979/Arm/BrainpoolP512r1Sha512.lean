module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hash

/-!
# Deterministic ECDSA over brainpoolP512r1 with HMAC-SHA-512 on 32-bit ARM

The hash function for the generic proof: SHA-512's functions that PBKDF2's
code calls (`Proof.Pbkdf2.Whole.Arm.sha512OKF`), and `vg_ecdsa_brainpoolp512r1_sign`,
with brainpoolP512r1's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcArm` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1Sha512

open VG VG.Arm

theorem implies :
    (rfcArm Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst 304).Implies
      (Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signContract Arm.abi 304) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR]
        all_goals simp only [Abi.constRegions, List.map_nil, List.not_mem_nil, false_implies, forall_const]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
        exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1, fun c hc => by cases hc⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, rfcArm,TablesOk,stkR] [satState 64 64] using satState 64 64 }

/-- SHA-512, for brainpoolP512r1's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcHash where
  R := brainpoolp512r1 hL
  I := Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst
  F := Proof.Pbkdf2.Whole.Arm.sha512F
  ok := Proof.Pbkdf2.Whole.Arm.sha512OKF
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha512.finalHash Spec.Sha512.H0_512 x).length = 64
    exact Proof.Hmac.Generic.Common.finalHash_length _ _
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  hDB := .inr (.inr (.inl ⟨rfl, rfl⟩))
  hS := Nat.le_of_ble_eq_true rfl
  hWi := Nat.le_of_ble_eq_true rfl
  hWf := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign (Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signContract Arm.abi 304) :=
  Arm.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1Sha512
