module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224

/-!
# Deterministic ECDSA over P-224 with HMAC-SHA-224 on x86 (32-bit)

The hash function for the generic proof, for any implementation `v` of
SHA-224's compression function: the functions that PBKDF2's code calls
(`Proof.Pbkdf2.Whole.X86.sha224OKF`), and `vg_ecdsa_p224_sign`,
with P-224's group law (`hL`, which the registration file supplies). The
shared contract implies `rfcWide` (`implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86.P224Sha224

open VG VG.X86

theorem implies :
    (rfcWide Spec.Ecdsa.Rfc6979.P224Sha224.inst 272).Implies
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract X86.abi 272) := by
  have a0 : arg (satState 28 28) 0 = 0x1000 := by decide
  have a1 : arg (satState 28 28) 1 = 0x2000 := by decide
  have a2 : arg (satState 28 28) 2 = 0x3000 := by decide
  have a3 : arg (satState 28 28) 3 = 0x8000 := by decide
  have e : argAddr (satState 28 28) 0 = 0x20004 := by decide
  have esp : (satState 28 28).gpr .esp = 0x20000 := rfl
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1, by simp⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes, rfcWide, rfcX86, TblsOk, Abi.constRegions, Abi.constsHeld, List.not_mem_nil, false_implies, implies_true] [a0, a1, a2, a3, e, esp]
          using satState 28 28 }

open VG.Proof.Sha256.X86.Variants (Backend)

/-- SHA-224 with the backend `v`, for P-224's group law `hL`. -/
def pack (hL : Weierstrass.Law Spec.P224.curve) (v : Backend) : RfcHash where
  R := p224 hL
  I := Spec.Ecdsa.Rfc6979.P224Sha224.inst
  F := v.F224
  ok := Proof.Pbkdf2.Whole.X86.sha224OKF v
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
  hS := show 96 ≤ 192 by decide
  hWi := show 104 * 8 ≤ 1872 by decide
  hWf := show 104 * 8 ≤ 1872 by decide
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve) (v : Backend) :
    Verified X86.target (cfgOf (pack hL v)).sign (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract X86.abi 272) :=
  X86.sign_verified (pack hL v) implies

end VG.Proof.Ecdsa.Rfc6979.X86.P224Sha224
