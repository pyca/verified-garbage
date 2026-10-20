module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT

/-!
# Deterministic ECDSA over brainpoolP384r1 with HMAC-SHA-384 on AArch64

SHA-384, with any implementation `v` of SHA-512's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signContract` for 256 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_brainpoolp384r1_sha384_sign` is verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sha384

open VG VG.AArch64
open VG.Proof.Sha512.AArch64 (Compress)

def sat : State := { satState 48 48 (fun _ => 0) 0 with
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 48⟩] }

theorem implies :
    (rfcAArch64 Impl.Ecdsa.AArch64.brainpoolp384r1 Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst 256).Implies
      (Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signContract AArch64.abi 256) := by
  sig_implies [Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP384r1.inst, Spec.BrainpoolP384r1.curve,
    Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, rfcAArch64, TblOk, tableRegions, tableAddr,
    Impl.Ecdsa.AArch64.brainpoolp384r1, Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, List.flatMap_nil, List.map_nil, List.flatten_nil, List.length_nil, brainpoolp384r1_empty_disjoint,
    List.not_mem_nil, false_implies, implies_true, forall_const, and_true, result,
    Spec.Ecdsa.Rfc6979.Instance.result, List.cons.injEq, below]
    [sat, satState] using sat

/-- SHA-384, with the implementation `v` of SHA-512's compression function. -/
def pack (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (hI : Weierstrass.AArch64.InvSounds) (v : Compress) :
    RfcHash where
  R := brainpoolp384r1 hL hI
  I := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst
  H := Proof.Pbkdf2.Md.AArch64.Sha512.hash v Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name Spec.Sha512.H0_384
  ok := Proof.Pbkdf2.Md.AArch64.Sha512.ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl
    (Or.inl rfl)
  C := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_coreOK
  satI := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_satI
  satF := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (hI : Weierstrass.AArch64.InvSounds) (v : Compress) :
    Verified AArch64.target (cfgOf (pack hL hI v)).sign
      (Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signContract AArch64.abi 256) :=
  Verified.of_correct (sign_a64 (pack hL hI v)) sign_ct implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sha384
