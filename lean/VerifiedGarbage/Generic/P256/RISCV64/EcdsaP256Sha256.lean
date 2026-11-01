module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P256Sha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-256 on RISC-V -/

@[expose] public section

namespace VG.Generic.P256.RISCV64.EcdsaP256Sha256

open VG.Proof.Ecdsa.Rfc6979.RISCV64.P256Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P256Sha256.signApi.artifact RISCV64.target {
    code := (pack h.law).c.sign
    stack := 544
    consts := Impl.Ecdsa.RISCV64.Comb.p256CombConsts
    verified := sign_verified h.law }]

end VG.Generic.P256.RISCV64.EcdsaP256Sha256
