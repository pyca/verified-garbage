module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P521Sha512
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on RISC-V -/

@[expose] public section

namespace VG.Generic.P521.RISCV64.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.RISCV64.P521Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P521Sha512.signApi.artifact RISCV64.target {
    code := (pack h.law).c.sign
    stack := 864
    verified := sign_verified h.law }]

end VG.Generic.P521.RISCV64.EcdsaP521Sha512
