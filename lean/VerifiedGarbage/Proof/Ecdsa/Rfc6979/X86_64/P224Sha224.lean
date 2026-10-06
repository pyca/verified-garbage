import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224

/-!
# Deterministic ECDSA over P-224 with HMAC-SHA-224 on x86-64

SHA-224, with any implementation `v` of SHA-256's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract` for 240 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p224_sha224_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P224Sha224

open VG VG.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

theorem implies :
    (rfcX86_64 Impl.Ecdsa.X86_64.p224.combConsts Spec.Ecdsa.Rfc6979.P224Sha224.inst 240).Implies
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract X86_64.abi 240) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64, TblsOk, p224_combConsts, Abi.constRegions, Abi.constsHeld,
          List.map_nil, List.append_nil, List.not_mem_nil, false_implies, implies_true, and_true]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1, fun c hc => by simp [p224_combConsts] at hc⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, satState] [satState 28 28] using satState 28 28 }

/-- SHA-224, with the implementation `v` of SHA-256's compression function. -/
def pack (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.X86_64.InvSounds) (v : Compress) : RfcHash where
  R := p224 hL hI
  I := Spec.Ecdsa.Rfc6979.P224Sha224.inst
  H := Proof.Pbkdf2.Md.X86_64.Sha224.hash v
  ok := Proof.Pbkdf2.Md.X86_64.Sha224.ok v
  C := Proof.Pbkdf2.Md.X86_64.Sha224.coreOK
  K := Proof.Pbkdf2.Md.X86_64.Sha224.callees v
  satI := Proof.Pbkdf2.Md.X86_64.Sha224.satI
  satF := Proof.Pbkdf2.Md.X86_64.Sha224.satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inr (.inr ⟨rfl, rfl⟩))
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl
  updSp := show Proof.Pbkdf2.Md.X86_64.Sha224.coreH.updC.allInstrs _ = true by decide +kernel

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    Verified X86_64.target (cfgOf (pack hL hI v)).sign
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract X86_64.abi 240) :=
  X86_64.sign_verified (pack hL hI v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.P224Sha224
