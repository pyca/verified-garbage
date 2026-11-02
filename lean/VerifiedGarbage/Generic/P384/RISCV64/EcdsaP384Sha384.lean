module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P384Sha384
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-384 with HMAC-SHA-384 on RISC-V -/

@[expose] public section

namespace VG.Generic.P384.RISCV64.EcdsaP384Sha384

open VG.Proof.Ecdsa.Rfc6979.RISCV64.P384Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P384Sha384.signApi.artifact RISCV64.target {
    code := (pack h.law).c.sign
    stack := 736
    verified := sign_verified h.law }]

end VG.Generic.P384.RISCV64.EcdsaP384Sha384
