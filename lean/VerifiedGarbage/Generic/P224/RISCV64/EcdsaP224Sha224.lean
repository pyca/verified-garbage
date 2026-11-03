module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P224Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on RISC-V -/

@[expose] public section

namespace VG.Generic.P224.RISCV64.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.RISCV64.P224Sha224 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact RISCV64.target {
    code := (pack h.law).c.sign
    consts := Impl.Ecdsa.RISCV64.Comb.p224CombConsts
    stack := 544
    verified := sign_verified h.law }]

end VG.Generic.P224.RISCV64.EcdsaP224Sha224
