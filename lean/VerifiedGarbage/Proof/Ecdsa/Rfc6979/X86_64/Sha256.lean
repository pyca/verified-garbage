import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-256 on x86-64

SHA-256, with any implementation `v` of its compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract` for 224 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p256_sha256_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.Sha256

open VG VG.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

theorem implies :
    (rfcX86_64 Spec.Ecdsa.Rfc6979.P256Sha256.inst).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract X86_64.abi 224) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, satState] [satState 32] using satState 32 }

/-- SHA-256, with the implementation `v` of its compression function. -/
def pack (v : Compress) : RfcHash where
  I := Spec.Ecdsa.Rfc6979.P256Sha256.inst
  H := Proof.Pbkdf2.Md.X86_64.Sha256.hash v
  ok := Proof.Pbkdf2.Md.X86_64.Sha256.ok v
  C := Proof.Pbkdf2.Md.X86_64.Sha256.coreOK
  K := Proof.Pbkdf2.Md.X86_64.Sha256.callees v
  satI := Proof.Pbkdf2.Md.X86_64.Sha256.satI
  satF := Proof.Pbkdf2.Md.X86_64.Sha256.satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inl ⟨rfl, rfl⟩
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  updSp := show Proof.Pbkdf2.Md.X86_64.Sha256.coreH.updC.allInstrs _ = true by decide +kernel

theorem sign_verified (v : Compress) :
    Verified X86_64.target (cfgOf (pack v)).sign
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract X86_64.abi 224) :=
  X86_64.sign_verified (pack v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.Sha256
