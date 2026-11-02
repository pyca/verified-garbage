module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P192Sha256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-192 with HMAC-SHA-256 on RISC-V -/

@[expose] public section

namespace VG.Generic.P192.RISCV64.EcdsaP192Sha256

open VG.Proof.Ecdsa.Rfc6979.RISCV64.P192Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P192Sha256.signApi.artifact RISCV64.target {
    code := (pack h.law).c.sign
    stack := 544
    verified := sign_verified h.law }]

end VG.Generic.P192.RISCV64.EcdsaP192Sha256
