module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP512r1
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT

/-!
# Deterministic ECDSA over brainpoolP512r1 with HMAC-SHA-512 on AArch64

SHA-512, with any implementation `v` of its compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signContract` for 320 bytes of stack
(`h` at the frame's top),
which implies the one the proof is written against (`implies`):
`vg_ecdsa_brainpoolp512r1_sha512_sign` is verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP512r1Sha512

open VG VG.AArch64
open VG.Proof.Sha512.AArch64 (Compress)

def sat : State := { satState 64 64 (fun _ => 0) 0 with
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩] }

theorem implies :
    (rfcAArch64 Impl.Ecdsa.AArch64.brainpoolp512r1 Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst 320).Implies
      (Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signContract AArch64.abi 320) := by
  sig_implies [Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP512r1.inst, Spec.BrainpoolP512r1.curve,
    Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, rfcAArch64, TblOk, tableRegions, tableAddr,
    Impl.Ecdsa.AArch64.brainpoolp512r1, Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, List.flatMap_nil, List.map_nil, List.flatten_nil, List.length_nil, brainpoolp512r1_empty_disjoint,
    List.not_mem_nil, false_implies, implies_true, forall_const, and_true, result,
    Spec.Ecdsa.Rfc6979.Instance.result, List.cons.injEq, below]
    [sat, satState] using sat

/-- SHA-512, with the implementation `v` of its compression function. -/
def pack (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds) (v : Compress) :
    RfcHash where
  R := brainpoolp512r1 hL hI
  I := Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst
  H := Proof.Pbkdf2.Md.AArch64.Sha512.hash v Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name Spec.Sha512.H0_512
  ok := Proof.Pbkdf2.Md.AArch64.Sha512.ok v rfl
    (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr rfl))) rfl (Or.inr (Or.inl rfl))
  C := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_coreOK
  satI := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_satI
  satF := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  hDB := .inr (.inr (.inl ⟨rfl, rfl⟩))
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds) (v : Compress) :
    Verified AArch64.target (cfgOf (pack hL hI v)).sign
      (Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signContract AArch64.abi 320) :=
  Verified.of_correct (sign_a64 (pack hL hI v)) sign_ct implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP512r1Sha512
