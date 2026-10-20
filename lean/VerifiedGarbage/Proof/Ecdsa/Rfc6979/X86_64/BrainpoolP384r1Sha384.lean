module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# Deterministic ECDSA over brainpoolP384r1 with HMAC-SHA-384 on x86-64

SHA-384, with any implementation `v` of SHA-512's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signContract` for 240 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_brainpoolp384r1_sha384_sign` is verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Sha384

open VG VG.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

theorem implies :
    (rfcX86_64 [] Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst 240).Implies
      (Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signContract X86_64.abi 240) := by
  sig_implies [Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP384r1.inst, Spec.BrainpoolP384r1.curve,
    Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, rfcX86_64, TblsOk,
    Abi.constRegions, Abi.constsHeld, stackBelow, List.forall_mem_nil,
    List.cons.injEq, List.not_mem_nil, false_implies, implies_true, forall_const, and_true, result, Spec.Ecdsa.Rfc6979.Instance.result]
    [satState] using (satState 48 48)

/-- SHA-384, with the implementation `v` of SHA-512's compression function. -/
def pack (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve)
    (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    RfcHash where
  R := brainpoolp384r1 hL hI
  I := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst
  H := Proof.Pbkdf2.Md.X86_64.Sha512.sha384H v
  ok := Proof.Pbkdf2.Md.X86_64.Sha512.sha384OK v
  C := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_coreOK
  K := Proof.Pbkdf2.Md.X86_64.Sha512.sha384K v
  satI := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_satI
  satF := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_satF
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
  updSp := show (Proof.Pbkdf2.Md.X86_64.Sha512.coreH 48).updC.allInstrs _ = true by decide +kernel

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve)
    (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    Verified X86_64.target (cfgOf (pack hL hI v)).sign
      (Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signContract X86_64.abi 240) :=
  X86_64.sign_verified (pack hL hI v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Sha384
