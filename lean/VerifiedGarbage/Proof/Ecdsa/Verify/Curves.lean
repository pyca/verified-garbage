module

public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1

/-!
# ECDSA verification of the hash function's output: the curves

Untrusted: everything here is checked by Lean. For each curve, `8 len` is
the number of bits of `n`, or 7 more for P-521 (`wide`), as
`hashToInt_fixedDigest` needs: the verification of each target writes the
`len` bytes of the hash it takes (`fixedDigest`) for these.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify

theorem p192_len : 8 * Spec.Ecdsa.P192.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.P192.inst.curve + if false then 7 else 0 := by
  have h₁ : 191 ≤ Spec.Ecdsa.P192.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.P192.inst.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.P192.inst.curve = Spec.Ecdsa.P192.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 24 = _
  rw [ite_eq_right Bool.false_ne_true]
  omega

theorem p224_len : 8 * Spec.Ecdsa.P224.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.P224.inst.curve + if false then 7 else 0 := by
  have h₁ : 223 ≤ Spec.Ecdsa.P224.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.P224.inst.curve.n.log2 < 224 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.P224.inst.curve = Spec.Ecdsa.P224.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 28 = _
  rw [ite_eq_right Bool.false_ne_true]
  omega

theorem p256_len : 8 * Spec.Ecdsa.P256.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.P256.inst.curve + if false then 7 else 0 := by
  have h₁ : 255 ≤ Spec.Ecdsa.P256.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.P256.inst.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.P256.inst.curve = Spec.Ecdsa.P256.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 32 = _
  rw [ite_eq_right Bool.false_ne_true]
  omega

theorem p384_len : 8 * Spec.Ecdsa.P384.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.P384.inst.curve + if false then 7 else 0 := by
  have h₁ : 383 ≤ Spec.Ecdsa.P384.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.P384.inst.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.P384.inst.curve = Spec.Ecdsa.P384.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 48 = _
  rw [ite_eq_right Bool.false_ne_true]
  omega

theorem p521_len : 8 * Spec.Ecdsa.P521.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.P521.inst.curve + if true then 7 else 0 := by
  have h₁ : 520 ≤ Spec.Ecdsa.P521.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.P521.inst.curve.n.log2 < 521 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.P521.inst.curve = Spec.Ecdsa.P521.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 66 = _
  rw [ite_eq_left rfl]
  omega

theorem secp256k1_len : 8 * Spec.Ecdsa.Secp256k1.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.Secp256k1.inst.curve + if false then 7 else 0 := by
  have h₁ : 255 ≤ Spec.Ecdsa.Secp256k1.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.Secp256k1.inst.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.Secp256k1.inst.curve = Spec.Ecdsa.Secp256k1.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 32 = _
  rw [ite_eq_right Bool.false_ne_true]
  omega

theorem brainpoolP256r1_len : 8 * Spec.Ecdsa.BrainpoolP256r1.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.BrainpoolP256r1.inst.curve + if false then 7 else 0 := by
  have h₁ : 255 ≤ Spec.Ecdsa.BrainpoolP256r1.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.BrainpoolP256r1.inst.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.BrainpoolP256r1.inst.curve = Spec.Ecdsa.BrainpoolP256r1.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 32 = _
  rw [ite_eq_right Bool.false_ne_true]
  omega

theorem brainpoolP384r1_len : 8 * Spec.Ecdsa.BrainpoolP384r1.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.BrainpoolP384r1.inst.curve + if false then 7 else 0 := by
  have h₁ : 383 ≤ Spec.Ecdsa.BrainpoolP384r1.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.BrainpoolP384r1.inst.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.BrainpoolP384r1.inst.curve = Spec.Ecdsa.BrainpoolP384r1.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 48 = _
  rw [ite_eq_right Bool.false_ne_true]
  omega

theorem brainpoolP512r1_len : 8 * Spec.Ecdsa.BrainpoolP512r1.inst.curve.len =
    Spec.Ecdsa.nBits Spec.Ecdsa.BrainpoolP512r1.inst.curve + if false then 7 else 0 := by
  have h₁ : 511 ≤ Spec.Ecdsa.BrainpoolP512r1.inst.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Ecdsa.BrainpoolP512r1.inst.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  have hn : Spec.Ecdsa.nBits Spec.Ecdsa.BrainpoolP512r1.inst.curve = Spec.Ecdsa.BrainpoolP512r1.inst.curve.n.log2 + 1 := rfl
  rw [hn]
  show 8 * 64 = _
  rw [ite_eq_right Bool.false_ne_true]
  omega

end VG.Proof.Ecdsa.Verify
