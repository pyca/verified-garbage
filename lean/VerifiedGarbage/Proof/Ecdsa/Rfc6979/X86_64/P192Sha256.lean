import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P192
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P192Sha256

/-!
# Deterministic ECDSA over p192 with HMAC-SHA-256 on x86-64

SHA-256, with any implementation `v` of SHA-256's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P192Sha256.inst.signContract` for 240 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p192_sha256_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P192Sha256

open VG VG.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

theorem implies :
    (rfcX86_64 [] Spec.Ecdsa.Rfc6979.P192Sha256.inst 240).Implies
      (Spec.Ecdsa.Rfc6979.P192Sha256.inst.signContract X86_64.abi 240) := by
  sig_implies [Spec.Ecdsa.Rfc6979.P192Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P192.inst, Spec.P192.curve,
    Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, rfcX86_64, TblsOk,
    Abi.constRegions, Abi.constsHeld, stackBelow, List.forall_mem_nil,
    List.cons.injEq, List.not_mem_nil, false_implies, implies_true, forall_const, and_true, result, Spec.Ecdsa.Rfc6979.Instance.result]
    [satState] using (satState 24 32)

/-- SHA-256, with the implementation `v` of SHA-256's compression function. -/
def pack (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    RfcHash where
  R := p192 hL hI
  I := Spec.Ecdsa.Rfc6979.P192Sha256.inst
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
  hQ := Nat.le_of_ble_eq_true rfl
  updSp := show Proof.Pbkdf2.Md.X86_64.Sha256.coreH.updC.allInstrs _ = true by decide +kernel

theorem sign_verified (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    Verified X86_64.target (cfgOf (pack hL hI v)).sign
      (Spec.Ecdsa.Rfc6979.P192Sha256.inst.signContract X86_64.abi 240) :=
  X86_64.sign_verified (pack hL hI v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.P192Sha256
