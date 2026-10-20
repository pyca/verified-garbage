module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP256r1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# Deterministic ECDSA over brainpoolP256r1 with HMAC-SHA-256 on x86 (32-bit)

The hash function for the generic proof, for any implementation `v` of
SHA-256's compression function: the functions that PBKDF2's code calls
(`Proof.Pbkdf2.Whole.X86.sha256OKF`), and `vg_ecdsa_brainpoolp256r1_sign`,
with brainpoolP256r1's group law and the soundness of the inversions (`hL`
and `hI`, which the registration file supplies). The
shared contract implies `rfcWide` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86.BrainpoolP256r1Sha256

open VG VG.X86

theorem implies :
    (rfcWide Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst 272).Implies
      (Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signContract X86.abi 272) := by
  have a0 : arg (satState 32 32) 0 = 0x1000 := by decide
  have a1 : arg (satState 32 32) 1 = 0x2000 := by decide
  have a2 : arg (satState 32 32) 2 = 0x3000 := by decide
  have a3 : arg (satState 32 32) 3 = 0x8000 := by decide
  have e : argAddr (satState 32 32) 0 = 0x20004 := by decide
  have esp : (satState 32 32).gpr .esp = 0x20000 := rfl
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1, by simp⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.BrainpoolP256r1.inst, Spec.BrainpoolP256r1.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true] [a0, a1, a2, a3, e, esp]
          using satState 32 32 }

open VG.Proof.Sha256.X86.Variants (Backend)

/-- SHA-256 with the backend `v`, for brainpoolP256r1's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) (v : Backend) : RfcHash where
  R := brainpoolp256r1 hL hI
  I := Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst
  F := v.F
  ok := Proof.Pbkdf2.Whole.X86.sha256OKF v
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha256.hash x).length = 32
    rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  hDB := .inl ⟨rfl, rfl⟩
  hS := show 96 ≤ 192 by decide
  hWi := show 104 * 8 ≤ 1872 by decide
  hWf := show 104 * 8 ≤ 1872 by decide
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) (v : Backend) :
    Verified X86.target (cfgOf (pack hL hI v)).sign (Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signContract X86.abi 272) :=
  X86.sign_verified (pack hL hI v) implies

end VG.Proof.Ecdsa.Rfc6979.X86.BrainpoolP256r1Sha256
