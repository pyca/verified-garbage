import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.Verified
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-256 on x86 (32-bit)

The hash function for the generic proof, for any implementation `v` of
SHA-256's compression function: the functions that PBKDF2's code calls
(`Proof.Pbkdf2.Whole.X86.sha256OKF`), and `vg_ecdsa_p256_sign`,
with P-256's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcWide` (`implies`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86.Sha256

open VG VG.X86

theorem implies :
    (rfcWide Spec.Ecdsa.Rfc6979.P256Sha256.inst).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract X86.abi 256) := by
  have a0 : arg (satState 32) 0 = 0x1000 := by decide
  have a1 : arg (satState 32) 1 = 0x2000 := by decide
  have a2 : arg (satState 32) 2 = 0x3000 := by decide
  have a3 : arg (satState 32) 3 = 0x8000 := by decide
  have e : argAddr (satState 32) 0 = 0x20004 := by decide
  have esp : (satState 32).gpr .esp = 0x20000 := rfl
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86] [a0, a1, a2, a3, e, esp]
          using satState 32 }

open VG.Proof.Sha256.X86.Variants (Backend)

/-- SHA-256 with the backend `v`, for P-256's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P256.curve) (v : Backend) : RfcHash where
  I := Spec.Ecdsa.Rfc6979.P256Sha256.inst
  F := v.F
  ok := Proof.Pbkdf2.Whole.X86.sha256OKF v
  ecdsa := rfl
  hash := rfl
  len := rfl
  macLen x := by
    show (Spec.Sha256.hash x).length = 32
    rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _
  tries := rfl
  hDB := .inl ⟨rfl, rfl⟩
  hS := show 96 ≤ 192 by decide
  hWi := show 104 * 8 ≤ 1872 by decide
  hWf := show 104 * 8 ≤ 1872 by decide
  coreX := Proof.Ecdsa.X86.sign_x86 hL
  coreCT := Proof.Ecdsa.X86.sign_ct

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve) (v : Backend) :
    Verified X86.target (cfgOf (pack hL v)).sign (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract X86.abi 256) :=
  X86.sign_verified (pack hL v) implies

end VG.Proof.Ecdsa.Rfc6979.X86.Sha256
